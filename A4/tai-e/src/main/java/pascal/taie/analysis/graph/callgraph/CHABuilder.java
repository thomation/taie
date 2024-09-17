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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        List<JMethod> worklist = new LinkedList<>();
        worklist.add(entry);
        while (!worklist.isEmpty()) {
            JMethod m = worklist.remove(0);
            if (callGraph.contains(m))
                continue;
            callGraph.addReachableMethod(m);
            for (Invoke cs : callGraph.getCallSitesIn(m)) {
                Set<JMethod> ms = resolve(cs);
                for (JMethod m1 : ms) {
                    callGraph.addEdge(new Edge<Invoke, JMethod>(CallGraphs.getCallKind(cs), cs, m1));
                    worklist.add(m1);
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> ret = new HashSet<>();
        MethodRef m = callSite.getMethodRef();
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC -> {
                ret.add(hierarchy.getJREMethod(m.toString()));
                break;
            }
            case SPECIAL -> {
                JClass c = m.getDeclaringClass();
                ret.add(dispatch(c, m.getSubsignature()));
                break;
            }
            case VIRTUAL -> {
                Set<JClass> classes = new HashSet<>();
                JClass me = m.getDeclaringClass();
                getAllSubclassesOf(me, classes);
                for (JClass c : classes)
                    ret.add(dispatch(c, m.getSubsignature()));
            }
            default -> {
                throw new RuntimeException("No case:" + CallGraphs.getCallKind(callSite));
            }
        }

        return ret;
    }

    private void getAllSubclassesOf(JClass jclass, Set<JClass> ret) {
        if (ret.contains(jclass))
            return;
        ret.add(jclass);
        for (JClass sub : hierarchy.getDirectSubclassesOf(jclass))
            getAllSubclassesOf(sub, ret);
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method != null && !method.isAbstract())
            return method;
        if (jclass.getSuperClass() != null) {
            method = dispatch(jclass.getSuperClass(), subsignature);
        }
        return method;
    }
}
