/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.inter;

import jas.CP;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.sql.Array;
import java.util.Collection;
import java.util.LinkedList;
import java.util.Optional;
import java.util.logging.FileHandler;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    private PointerAnalysisResult ptaResult;

    public static class FieldHelper
    {
        public FieldHelper(Obj obj, JField field, Var value) {
            this.obj = obj;;
            this.field = field;
            this.value = value;
        }
        public boolean match(Obj obj, JField field) {
            return this.obj == obj && this.field == field;
        }
        public Var getValue() {
            return value;
        }
        private final Obj obj;
        private final JField field;
        private final Var value;
    }
    LinkedList<FieldHelper> fieldHelperList = new LinkedList<>();
    public static class ArrayHelper {
        public ArrayHelper(Obj obj, Var index, Var value) {
            this.obj = obj;
            this.index = index;
            this.value = value;
        }
        public boolean match(Obj obj) {
            return this.obj == obj;
        }
        private final Obj obj;
        private final Var index;
        private final Var value;
    }
    LinkedList<ArrayHelper> arrayHelperList = new LinkedList<>();
    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        ptaResult = World.get().getResult(ptaId);
        // You can do initialization work here
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // LIB4
        return cp.transferNode(stmt, in, out);
    }
    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // LIB7
        boolean change =  cp.transferNode(stmt, in, out);
        if(stmt instanceof StoreField storeField) {
            handleStoreField(storeField);
        } else if(stmt instanceof LoadField loadField) {
            change |= handleLoadField(loadField, out);
        } else if(stmt instanceof StoreArray storeArray) {
            handleStoreArray(storeArray);
        } else if(stmt instanceof LoadArray loadArray) {
            change |= handleLoadArray(loadArray, out);
        }
        return change;
    }
    private void handleStoreField(StoreField storeField) {
        if (storeField.getDef().isEmpty()) {
            return;
        }
        LValue def = storeField.getDef().get();
        if (def instanceof InstanceFieldAccess instanceFieldAccess) {
            for (Obj o : ptaResult.getPointsToSet(instanceFieldAccess.getBase())) {
                System.out.println(o);
                Var rValue = (Var)storeField.getRValue(); // TODO: RValue is not a Var?
                fieldHelperList.add(new FieldHelper(o, instanceFieldAccess.getFieldRef().resolveNullable(), rValue));
            }
        }
    }
    private boolean handleLoadField(LoadField stmt, CPFact out) {
        boolean change = false;
        if (stmt.getDef().isEmpty()) {
            return change;
        }
        LValue def = stmt.getDef().get();
        if(def instanceof Var var) {
            for (Exp exp : stmt.getUses()) {
                if (exp instanceof InstanceFieldAccess instanceFieldAccesExp) {
                    Collection<InstanceField> fields =  ptaResult.getInstanceFields();
                    for(Obj o :ptaResult.getPointsToSet(instanceFieldAccesExp.getBase()))
                    {
                        System.out.println(o);
                        Collection<CSObj> csobjs = ptaResult.getCSObjects();
                        for(CSObj cso : csobjs) {
                            if(cso.getObject() == o) {
                                System.out.println("get csobj");
                                for(InstanceField field: fields) {
                                    if(field.getBase() == cso) {
                                        System.out.println("get filed");
                                        for(FieldHelper fh: fieldHelperList) {
                                            if(fh.match(o, field.getField())) {
                                                System.out.println(fh.getValue());
                                                out.update(var, out.get(fh.getValue()));
                                                change = true;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return change;
    }
    private void handleStoreArray(StoreArray storeArray) {
        if (storeArray.getDef().isEmpty()) {
            return;
        }
        LValue def = storeArray.getDef().get();
        if (def instanceof ArrayAccess arrayAccess) {
            for(Obj o: ptaResult.getPointsToSet(arrayAccess.getBase())) {
                System.out.println(o);
                Var index = arrayAccess.getIndex();
                Var rValue = (Var)storeArray.getRValue();
                arrayHelperList.add(new ArrayHelper(o, index, rValue));
            }
        }
    }
    private boolean handleLoadArray(LoadArray stmt, CPFact out) {
        boolean change = false;
        if (stmt.getDef().isEmpty()) {
            return change;
        }
        LValue def = stmt.getDef().get();
        if(def instanceof Var var) {
            ArrayAccess arrayAccess = stmt.getArrayAccess();
            Var index = arrayAccess.getIndex();
            for(Obj o: ptaResult.getPointsToSet(arrayAccess.getBase())) {
                for(ArrayHelper arrayHelper: arrayHelperList) {
                    if(arrayHelper.match(o) && out.get(index) == out.get(arrayHelper.index)) {
                        System.out.println(arrayHelper);
                        out.update(var, out.get(arrayHelper.value));
                        change = true;
                    }
                }
            }
        }
        return change;
    }
    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // LIB4
        CPFact ret = out.copy();
        return ret;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // LIB4
        CPFact ret = out.copy();
        Optional<LValue> def = edge.getSource().getDef();
        def.ifPresent(lValue -> ret.update((Var) lValue, Value.getUndef()));
        return ret;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // LIB4
        CPFact ret = new CPFact();
        JMethod m = edge.getCallee();
        Invoke source = (Invoke) edge.getSource();
        for(int i = 0; i < m.getIR().getParams().size(); i ++) {
            Var v = m.getIR().getParam(i);
            Var a = source.getInvokeExp().getArg(i);
            ret.update(v, callSiteOut.get(a));
        }
        return ret;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // LIB4
        CPFact ret = new CPFact();
        Optional<LValue> def = edge.getCallSite().getDef();
        if(def.isPresent()) {
            for(Var v: edge.getReturnVars()) {
                ret.update((Var)def.get(), returnOut.get(v));
                ret.update(v, Value.getUndef());
                break;
            }
        }
        return ret;
    }
}
