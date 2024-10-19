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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;


class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // LAB5
        if(callGraph.contains(method))
            return;
        callGraph.addReachableMethod(method);
        for(Stmt stmt : method.getIR().getStmts()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // LAB5
        public Void visit(New stmt) {
            Pointer p = pointerFlowGraph.getVarPtr(stmt.getLValue());
            PointsToSet set = new PointsToSet();
            Obj o = heapModel.getObj(stmt);
            set.addObject(o);
            workList.addEntry(p, set);
            return null;
        }
        public Void visit(Copy stmt) {
            Pointer left = pointerFlowGraph.getVarPtr(stmt.getLValue());
            Pointer right = pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(right, left);
            return null;
        }
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()) {
                Pointer left = pointerFlowGraph.getVarPtr(stmt.getLValue());
                Pointer right = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(right, left);
            }
            return null;
        }

        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) {
                Pointer left = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                Pointer right = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(right, left);
            }
            return null;
        }
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()) {

            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // LAB5
        if(pointerFlowGraph.addEdge(source, target)) {
            PointsToSet set = source.getPointsToSet();
            if(set != null && !set.isEmpty())
                workList.addEntry(target, set);
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // LAB5
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = new PointsToSet();
            Pointer n = entry.pointer();
            for(Obj obj: entry.pointsToSet()) {
                if(!n.getPointsToSet().contains(obj))
                    delta.addObject(obj);
            }
            propagate(n, delta);
            if(n instanceof VarPtr) {
                for(Obj o: delta) {
                    Var x = ((VarPtr) n).getVar();
                    for (StoreField sf : x.getStoreFields()) {
                        Pointer y = pointerFlowGraph.getVarPtr(sf.getRValue());
                        JField f = sf.getFieldRef().resolve();
                        Pointer of = pointerFlowGraph.getInstanceField(o, f);
                        addPFGEdge(y, of);
                    }
                    for(LoadField lf: x.getLoadFields()) {
                        Pointer y = pointerFlowGraph.getVarPtr(lf.getLValue());
                        JField f = lf.getFieldRef().resolve();
                        Pointer of = pointerFlowGraph.getInstanceField(o, f);
                        addPFGEdge(of, y);
                    }
                    processCall(x, o);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // LAB5
        if(pointsToSet.isEmpty())
            return null;
        for(Obj obj: pointsToSet)
            pointer.getPointsToSet().addObject(obj);
        for(Pointer t: pointerFlowGraph.getSuccsOf(pointer))
            workList.addEntry(t, pointsToSet);
        return null;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // LAB5
        for(Invoke invoke : var.getInvokes()) {
            JMethod m = resolveCallee(recv, invoke);
            Pointer tp = pointerFlowGraph.getVarPtr(m.getIR().getThis());
            workList.addEntry(tp, new PointsToSet(recv));
            if(callGraph.addEdge(new Edge<Invoke, JMethod>(CallGraphs.getCallKind(invoke), invoke, m))) {
                addReachable(m);
                for(int i = 0; i < m.getIR().getParams().size(); i ++) {
                    Var p = m.getIR().getParam(i);
                    Var a = invoke.getInvokeExp().getArg(i);
                    addPFGEdge(pointerFlowGraph.getVarPtr(a), pointerFlowGraph.getVarPtr(p));
                }
                for(Var mr : m.getIR().getReturnVars()) {
                    Var r = invoke.getResult();
                    addPFGEdge(pointerFlowGraph.getVarPtr(mr), pointerFlowGraph.getVarPtr(r));
                }
            }

        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
