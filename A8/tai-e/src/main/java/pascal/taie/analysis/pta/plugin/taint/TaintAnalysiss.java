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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // LIB8
        // You could query pointer analysis results you need via variable result.
        var methods = result.getCSCallGraph().reachableMethods();
        methods.forEach(m -> hanldeCSMethod(m, taintFlows));
        return taintFlows;
    }
    private void hanldeCSMethod(CSMethod csMethod, Set<TaintFlow> taintFlows) {
        var method = csMethod.getMethod();
        for(int i = 0; i < method.getParamCount(); i ++) {
            for(var sink :config.getSinks()) {
                if(sink.method() == method && sink.index() == i) {
                    handleSink(csMethod, i, taintFlows);
                }
            }

        }
    }
    private void handleSink(CSMethod csMethod, int i, Set<TaintFlow> taintFlows) {
        var method = csMethod.getMethod();
        // get pt(c:ai)
        PointerAnalysisResult result = solver.getResult();
        for(var caller: result.getCSCallGraph().getCallersOf(csMethod)) {
            var l = caller.getCallSite();
            var arg = l.getInvokeExp().getArg(i);
            var pts = result.getPointsToSet(arg);
            for(var obj : pts) {
                if (manager.isTaint(obj)) {
                    var j = manager.getSourceCall(obj);
                    var f = new TaintFlow(j, l, i);
                    taintFlows.add(f);
                }
            }
        }
    }
    public boolean isSource(JMethod method, Type type) {
        for(var source: config.getSources()) {
            if(source.method() == method && source.type() == type)
                return true;
        }
        return false;
    }
    public Obj makeTaint(Invoke source, Type type) {
       return manager.makeTaint(source, type);
    }
}
