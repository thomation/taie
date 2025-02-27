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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.List;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        List<Node> worklist = new LinkedList<Node>();
        for (Node node : cfg) {
            if (cfg.isEntry(node))
                continue;
            worklist.add(node);
        }
        while (!worklist.isEmpty()) {
            Node node = worklist.remove(0);
            Fact in = analysis.newInitialFact();
            for (Node pre : cfg.getPredsOf(node)) {
                analysis.meetInto(result.getOutFact(pre), in);
            }
            result.setInFact(node, in);
            if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                for(Node succ: cfg.getSuccsOf(node)) {
                    worklist.add(succ);
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        List<Node> worklist = new LinkedList<>();
        for(Node node : cfg) {
            if(cfg.isExit(node))
                continue;
            worklist.add(node);
        }
        while (!worklist.isEmpty()) {
            Node node = worklist.remove(0);
            Fact out = analysis.newInitialFact();
            for (Node succ : cfg.getSuccsOf(node)) {
                analysis.meetInto(result.getInFact(succ), out);
            }
            result.setOutFact(node, out);
            if(analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                for(Node pre: cfg.getPredsOf(node)) {
                    worklist.add(pre);
                }
            }
        }
    }
}
