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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.util.collection.SetQueue;

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        Node entry = getEntryNode();
        result.setOutFact(entry, analysis.newBoundaryFact(entry));
        for (Node node : icfg) {
            if (node.equals(entry))
                continue;
            ;
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }
    }

    Node getEntryNode() {
        for (Method m : icfg.entryMethods().toList()) {
            Node node = icfg.getEntryOf(m);
            return node;
        }
        throw new RuntimeException("No entry node");
    }

    private void doSolve() {
        Node entry = getEntryNode();
        List<Node> worklist = new LinkedList<Node>();
        for (Node node : icfg) {
            if (node.equals(entry))
                continue;
            worklist.add(node);
        }
        while (!worklist.isEmpty()) {
            Node node = worklist.remove(0);
            Fact in = analysis.newInitialFact();
            for(ICFGEdge<Node> edge : icfg.getInEdgesOf(node) ) {
                if (edge instanceof NormalEdge) {
                    analysis.meetInto(result.getOutFact(edge.getSource()), in);
                } else if (edge instanceof CallToReturnEdge) {
                    analysis.meetInto(result.getOutFact(edge.getSource()), in);
                } else if (edge instanceof CallEdge) {
                    analysis.meetInto(result.getOutFact(edge.getSource()), in);
                } else {
                    analysis.meetInto(result.getOutFact(edge.getSource()), in);
                }
            }
            result.setInFact(node, in);
            if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                for(ICFGEdge<Node> edge : icfg.getOutEdgesOf(node)) {
                    worklist.add(edge.getTarget());
                }
            }
        }
    }
}
