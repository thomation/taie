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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import soot.JastAddJ.Opt;
import soot.jimple.IfStmt;

import javax.swing.text.html.Option;
import java.util.Comparator;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set<Stmt> reachable = computeReachableStmt(cfg, constants);
        for (Stmt stmt : cfg) {
            if (cfg.isEntry(stmt) || cfg.isExit(stmt))
                continue;
            if (!reachable.contains(stmt)) {
                deadCode.add(stmt);
                continue;
            }
            // Check dead assign
            if (stmt.getDef().isEmpty())
                continue;
            Var def = (Var) stmt.getDef().get();
            SetFact<Var> lives = liveVars.getResult(stmt);
            if (!lives.contains(def)) {
                deadCode.add(stmt);
            }
        }
        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    Set<Stmt> computeReachableStmt(CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants) {
        Set<Stmt> reach = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Stmt entry = cfg.getEntry();
        computeReachableStmt(cfg, entry, constants, reach);
        return reach;
    }

    void computeReachableStmt(CFG<Stmt> cfg, Stmt node, DataflowResult<Stmt, CPFact> constants, Set<Stmt> reach) {
        // Caused by goto.
        if(reach.contains(node))
            return;
        reach.add(node);
        if (node instanceof If) {
            handleIfStmt(cfg, (If) node, constants, reach);
        } else if (node instanceof SwitchStmt) {
            handleSwitchStmt(cfg, (SwitchStmt)node, constants, reach);
        } else {
            handleNormalStmt(cfg, node, constants, reach);
        }
    }

    void handleIfStmt(CFG<Stmt> cfg, If ifNode, DataflowResult<Stmt, CPFact> constants, Set<Stmt> reach) {
        CPFact constantsResult = constants.getResult(ifNode);
        ConditionExp exp = ifNode.getCondition();
        Optional<Value> constValue = checkConditonConst(exp, constantsResult);
        Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(ifNode);
        for (Edge<Stmt> outEdge : outEdges) {
            if (constValue.isPresent()) {
                if (outEdge.getKind() == Edge.Kind.IF_TRUE && constValue.get().getConstant() == 0)
                    continue;
                if (outEdge.getKind() == Edge.Kind.IF_FALSE && constValue.get().getConstant() == 1)
                    continue;
            }
            computeReachableStmt(cfg, outEdge.getTarget(), constants, reach);
        }
    }

    Optional<Value> checkConditonConst(ConditionExp exp, CPFact constants) {
        Var left = exp.getOperand1();
        Var right = exp.getOperand2();
        Optional<Value> v1 = checkVarConst(left, constants);
        Optional<Value> v2 = checkVarConst(right, constants);
        if (v1.isPresent() && v2.isPresent()) {
            return Optional.of(ConstantPropagation.evaluateConditionExp(exp, v1.get(), v2.get()));
        }
        return Optional.ofNullable(null);
    }

    Optional<Value> checkVarConst(Var var, CPFact constants) {
        Value v = constants.get(var);
        if (v != null && v.isConstant())
            return Optional.of(v);
        return Optional.ofNullable(null);
    }
    void handleSwitchStmt(CFG<Stmt> cfg, SwitchStmt node, DataflowResult<Stmt, CPFact> constants, Set<Stmt> reach) {
        CPFact constantsResult = constants.getResult(node);
        Var var = node.getVar();
        Optional<Value> v = checkVarConst(var, constantsResult);
        Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(node);
        int i = -1;
        boolean match = false;
        for (Edge<Stmt> outEdge : outEdges) {
            i ++;
            if(v.isPresent()) {
                if(outEdge.getKind() == Edge.Kind.SWITCH_CASE) {
                    Integer c = node.getCaseValues().get(i);
                    if(c != v.get().getConstant())
                        continue;
                    match = true;
                }
                if(outEdge.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                    if(match)
                        continue;
                }
                computeReachableStmt(cfg, outEdge.getTarget(), constants, reach);
            }
        }
    }

    void handleNormalStmt(CFG<Stmt> cfg, Stmt node, DataflowResult<Stmt, CPFact> constants, Set<Stmt> reach) {
        Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(node);
        for (Edge<Stmt> outEdge : outEdges) {
            if (outEdge.getKind() == Edge.Kind.RETURN)
                continue;
            computeReachableStmt(cfg, outEdge.getTarget(), constants, reach);
        }
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
