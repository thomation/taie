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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import java.util.List;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact ret = new CPFact();
        List<Var> params = cfg.getIR().getParams();
        if (params != null && !params.isEmpty()) {
            for (Var param : params) {
                ret.update(param, Value.getNAC());
            }
        }
        return ret;
    }


    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var k : fact.keySet()) {
            Value s = fact.get(k);
            Value t = target.get(k);
            Value v = meetValue(s, t);
            target.update(k, v);
        }
    }


    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC())
            return Value.getNAC();
        if (v1.isUndef())
            return v2;
        if (v2.isUndef())
            return v1;
        if (!v1.equals(v2))
            return Value.getNAC();

        return v1;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact newOut = in.copy();
        if (!stmt.getDef().isEmpty()) {
            Var def = (Var) stmt.getDef().get();
            for (Exp exp : stmt.getUses()) {
                Value newValue = evaluate(exp, in);
                newOut.update(def, newValue);
            }
        }
        boolean change = !newOut.equals(out);
        out.clear();
        out.copyFrom(newOut);
        return change;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral cv) {
            return Value.makeConstant(cv.getValue());
        }
        if (exp instanceof Var var) {
            return in.get(var);
        }
        if (exp instanceof BinaryExp be) {
            return evaluateBinaryExp(be, in);
        }
        if(exp instanceof  InvokeVirtual iv) {
            return Value.getNAC();
        }
        return Value.getUndef();
    }

    static Value evaluateBinaryExp(BinaryExp exp, CPFact in) {
        Var op1 = exp.getOperand1();
        Var op2 = exp.getOperand2();
        Value v1 = in.get(op1);
        Value v2 = in.get(op2);
        if (v1.isConstant() && v2.isConstant()) {
            if (exp instanceof ArithmeticExp abe) {
                return evaluateArithmeticExp(abe, v1, v2);
            } else if (exp instanceof BitwiseExp bwe) {
                return evaluateBitwiseExp(bwe, v1, v2);
            } else if (exp instanceof ConditionExp ce) {
                return evaluateConditionExp(ce, v1, v2);
            } else if (exp instanceof ShiftExp se) {
                return evaluateShiftExp(se, v1, v2);
            }
            throw new UnsupportedOperationException();
        }
        if (v1.isNAC() || v2.isNAC())
            return Value.getNAC();
        return Value.getUndef();
    }

    static Value evaluateArithmeticExp(ArithmeticExp exp, Value v1, Value v2) {
        int ret = 0;
        int left = v1.getConstant();
        int right = v2.getConstant();
        switch (exp.getOperator()) {
            case ADD -> ret = left + right;
            case SUB -> ret = left - right;
            case MUL -> ret = left * right;
            case DIV -> ret = left / right;
            case REM -> ret = left % right;
        }
        return Value.makeConstant(ret);
    }

    static Value evaluateBitwiseExp(BitwiseExp exp, Value v1, Value v2) {
        int ret = 0;
        int left = v1.getConstant();
        int right = v2.getConstant();
        switch (exp.getOperator()) {
            case AND -> ret = left & right;
            case OR -> ret = left | right;
            case XOR -> ret = left ^ right;
        }
        return Value.makeConstant(ret);
    }

    static Value evaluateConditionExp(ConditionExp exp, Value v1, Value v2) {
        boolean ret = false;
        int left = v1.getConstant();
        int right = v2.getConstant();
        switch (exp.getOperator()) {
            case EQ -> ret = left == right;
            case NE -> ret = left != right;
            case LT -> ret = left < right;
            case GT -> ret = left > right;
            case LE -> ret = left <= right;
            case GE -> ret = left >= right;
        }
        int value = ret ? 1 : 0;
        return Value.makeConstant(value);
    }

    static Value evaluateShiftExp(ShiftExp exp, Value v1, Value v2) {
        int ret = 0;
        int left = v1.getConstant();
        int right = v2.getConstant();
        switch (exp.getOperator()) {
            case SHL -> ret = left << right;
            case SHR -> ret = left >> right;
            case USHR -> ret = left >>> right;
        }
        return Value.makeConstant(ret);
    }
}
