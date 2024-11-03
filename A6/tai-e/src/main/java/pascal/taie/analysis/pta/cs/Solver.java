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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // LAB6
        if(callGraph.contains(csMethod))
            return;
        callGraph.addReachableMethod(csMethod);
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        for(Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }
        // LAB6
        public Void visit(New stmt) {
            Pointer p = csManager.getCSVar(context, stmt.getLValue());
            Obj o = heapModel.getObj(stmt);
            CSObj co = csManager.getCSObj(context, o);
            PointsToSet set = PointsToSetFactory.make(co);
            workList.addEntry(p, set);
            return null;
        }
        public Void visit(Copy stmt) {
            Pointer left = csManager.getCSVar(context, stmt.getLValue());
            Pointer right = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(right, left);
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // LAB6
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
        // LAB6
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = PointsToSetFactory.make();
            Pointer n = entry.pointer();
            for(CSObj obj: entry.pointsToSet()) {
                if(!n.getPointsToSet().contains(obj))
                    delta.addObject(obj);
            }
            propagate(n, delta);
            if(n instanceof CSVar csn) {
                for(CSObj o: delta) {
                    Var x = csn.getVar();
                    for (StoreField sf : x.getStoreFields()) {
                        Pointer y = csManager.getCSVar(csn.getContext(), sf.getRValue());
                        JField f = sf.getFieldRef().resolve();
                        Pointer of = csManager.getInstanceField(o, f);
                        addPFGEdge(y, of);
                    }
                    for(LoadField lf: x.getLoadFields()) {
                        Pointer y = csManager.getCSVar(csn.getContext(), lf.getLValue());
                        JField f = lf.getFieldRef().resolve();
                        Pointer of = csManager.getInstanceField(o, f);
                        addPFGEdge(of, y);
                    }
                    for (StoreArray sa : x.getStoreArrays()) {
                        Pointer y = csManager.getCSVar(csn.getContext(), sa.getRValue());
                        ArrayIndex ai = csManager.getArrayIndex(o);
                        addPFGEdge(y, ai);
                    }
                    for (LoadArray la : x.getLoadArrays()) {
                        Pointer y = csManager.getCSVar(csn.getContext(), la.getLValue());
                        ArrayIndex ai = csManager.getArrayIndex(o);
                        addPFGEdge(ai, y);
                    }
                    processCall(csn, o);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // LAB6
        if(pointsToSet.isEmpty())
            return null;
        for(CSObj obj: pointsToSet)
            pointer.getPointsToSet().addObject(obj);
        for(Pointer t: pointerFlowGraph.getSuccsOf(pointer))
            workList.addEntry(t, pointsToSet);
        return pointer.getPointsToSet();
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
