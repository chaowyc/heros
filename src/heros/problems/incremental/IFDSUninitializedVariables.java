package heros.problems.incremental;

/* Soot - a J*va Optimization Framework
 * Copyright (C) 1997-2013 Eric Bodden and others
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */

import heros.FlowFunction;
import heros.FlowFunctions;
import heros.flowfunc.Identity;
import heros.flowfunc.KillAll;
import heros.incremental.UpdatableInterproceduralCFG;
import heros.incremental.UpdatableWrapper;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import soot.Local;
import soot.NullType;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.DefinitionStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.ThrowStmt;
import soot.jimple.internal.JimpleLocal;
import heros.template.DefaultUpdatableJimpleIFDSTabulationProblem;
import soot.util.Chain;

public class IFDSUninitializedVariables extends DefaultUpdatableJimpleIFDSTabulationProblem<UpdatableWrapper<Local>,
        UpdatableInterproceduralCFG<Unit, SootMethod>> {

    public IFDSUninitializedVariables(UpdatableInterproceduralCFG<Unit, SootMethod> icfg) {
        super(icfg);
    }

    @Override
    public FlowFunctions<UpdatableWrapper<Unit>, UpdatableWrapper<Local>, UpdatableWrapper<SootMethod>> createFlowFunctionsFactory() {
        return new FlowFunctions<UpdatableWrapper<Unit>, UpdatableWrapper<Local>, UpdatableWrapper<SootMethod>>() {

            @Override
            public FlowFunction<UpdatableWrapper<Local>> getNormalFlowFunction
                    (final UpdatableWrapper<Unit> curr, UpdatableWrapper<Unit> succ) {

                final UpdatableWrapper<SootMethod> m = interproceduralCFG().getMethodOf(curr);
                if(Scene.v().getEntryPoints().contains(m) && interproceduralCFG().isStartPoint(curr)) {
                    return new FlowFunction<UpdatableWrapper<Local>>() {

                        @Override
                        public Set<UpdatableWrapper<Local>> computeTargets(UpdatableWrapper<Local> source) {
                            if (source == zeroValue()) {
                                Set<Local> res = new LinkedHashSet<Local>();
                                res.addAll(m.getContents().getActiveBody().getLocals());
                                for (int i=0; i < m.getContents().getParameterCount(); i++)
                                    res.remove(m.getContents().getActiveBody().getParameterLocal(i));
                                return interproceduralCFG().wrap(res);
                            }
                            return Collections.emptySet();
                        }
                    };
                }

                if (curr.getContents() instanceof DefinitionStmt) {
                    return new FlowFunction<UpdatableWrapper<Local>>() {

                        @Override
                        public Set<UpdatableWrapper<Local>> computeTargets(final UpdatableWrapper<Local> source) {
                            final DefinitionStmt definition = (DefinitionStmt) curr.getContents();
                            final Value leftOp = definition.getLeftOp();
                            if(leftOp instanceof Local) {
                                final Local leftOpLocal = (Local) leftOp;

                                List<ValueBox> useBoxes = definition.getUseBoxes();
                                for (ValueBox valueBox : useBoxes) {
                                    if (valueBox.getValue().equivTo(source.getContents())) {
                                        LinkedHashSet<Local> res = new LinkedHashSet<Local>();
                                        res.add(source.getContents());
                                        res.add(leftOpLocal);
                                        return interproceduralCFG().wrap(res);
                                    }
                                }

                                if (leftOp.equivTo(source.getContents()))
                                    return Collections.emptySet();
                            }
                            return Collections.singleton(source);
                        }
                    };
                }

                return Identity.v();
            }

            @Override
            public FlowFunction<UpdatableWrapper<Local>> getCallFlowFunction
                    (UpdatableWrapper<Unit> callStmt, final UpdatableWrapper<SootMethod> destinationMethod) {
                Stmt stmt = (Stmt) callStmt.getContents();
                InvokeExpr invokeExpr = stmt.getInvokeExpr();
                final List<UpdatableWrapper<Value>> args = interproceduralCFG().wrap(invokeExpr.getArgs());

                final List<UpdatableWrapper<Local>> localArguments = new ArrayList<UpdatableWrapper<Local>>();
                for (UpdatableWrapper<Value> value : args)
                    if (value.getContents() instanceof Local)
                        localArguments.add(interproceduralCFG().wrap((Local) value.getContents()));

                return new FlowFunction<UpdatableWrapper<Local>>() {

                    @Override
                    public Set<UpdatableWrapper<Local>> computeTargets
                            (final UpdatableWrapper<Local> source) {
                        // Dot not map parameters for <clinit> edges
                        if (destinationMethod.getContents().getName().equals("<clinit>"))
                            return Collections.emptySet();

                        for (UpdatableWrapper<Local> localArgument : localArguments) {
                            if (source.getContents().equivTo(localArgument.getContents())) {
                                return Collections.<UpdatableWrapper<Local>>singleton
                                        (interproceduralCFG().wrap(destinationMethod.getContents().getActiveBody().getParameterLocal
                                                (args.indexOf(localArgument))));
                            }
                        }

                        if (source == zeroValue()) {
                            //gen all locals that are not parameter locals
                            Chain<Local> locals = destinationMethod.getContents().getActiveBody().getLocals();
                            LinkedHashSet<Local> uninitializedLocals = new LinkedHashSet<Local>(locals);
                            for (int i = 0; i < destinationMethod.getContents().getParameterCount(); i++) {
                                uninitializedLocals.remove(destinationMethod.getContents().getActiveBody().getParameterLocal(i));
                            }
                            return interproceduralCFG().wrap(uninitializedLocals);
                        }

                        return Collections.emptySet();
                    }

                };
            }

            @Override
            public FlowFunction<UpdatableWrapper<Local>> getReturnFlowFunction
                    (final UpdatableWrapper<Unit> callSite,
                     final UpdatableWrapper<SootMethod> calleeMethod,
                     final UpdatableWrapper<Unit> exitStmt,
                     final UpdatableWrapper<Unit> returnSite) {
                if (callSite.getContents() instanceof DefinitionStmt) {
                    DefinitionStmt definition = (DefinitionStmt) callSite.getContents();
                    if(definition.getLeftOp() instanceof Local) {
                        final UpdatableWrapper<Local> leftOpLocal = interproceduralCFG().wrap
                                ((Local) definition.getLeftOp());
                        if (exitStmt.getContents() instanceof ReturnStmt) {
                            final UpdatableWrapper<ReturnStmt> returnStmt = interproceduralCFG().wrap
                                    ((ReturnStmt) exitStmt.getContents());
                            return new FlowFunction<UpdatableWrapper<Local>>() {

                                @Override
                                public Set<UpdatableWrapper<Local>> computeTargets
                                        (UpdatableWrapper<Local> source) {
                                    if (returnStmt.getContents().getOp().equivTo(source.getContents()))
                                        return Collections.singleton(leftOpLocal);
                                    return Collections.emptySet();
                                }

                            };
                        } else if (exitStmt instanceof ThrowStmt) {
                            //if we throw an exception, LHS of call is undefined
                            return new FlowFunction<UpdatableWrapper<Local>>() {

                                @Override
                                public Set<UpdatableWrapper<Local>> computeTargets
                                        (final UpdatableWrapper<Local> source) {
                                    if (source == zeroValue())
                                        return Collections.singleton(leftOpLocal);
                                    else
                                        return Collections.emptySet();
                                }

                            };
                        }
                    }
                }

                return KillAll.v();
            }

            @Override
            public FlowFunction<UpdatableWrapper<Local>> getCallToReturnFlowFunction
                    (UpdatableWrapper<Unit> callSite, UpdatableWrapper<Unit> returnSite) {
                if (callSite.getContents() instanceof DefinitionStmt) {
                    final UpdatableWrapper<DefinitionStmt> definition = interproceduralCFG().wrap
                            ((DefinitionStmt) callSite.getContents());
                    if(definition.getContents().getLeftOp() instanceof Local) {
                        return new FlowFunction<UpdatableWrapper<Local>>() {

                            @Override
                            public Set<UpdatableWrapper<Local>> computeTargets(
                                    UpdatableWrapper<Local> source) {
                                final Local leftOpLocal = (Local) definition.getContents().getLeftOp();
                                if (source == interproceduralCFG().wrap(leftOpLocal))
                                    return Collections.emptySet();
                                return Collections.singleton(source);
                            }

                        };
                    }
                }
                return Identity.v();
            }
        };
    }
    @Override
    public Set<UpdatableWrapper<Unit>> initialSeeds() {
        return Collections.singleton(this.interproceduralCFG().wrap
                (Scene.v().getMainMethod().getActiveBody().getUnits().getFirst()));
    }

    @Override
    public UpdatableWrapper<Local> createZeroValue() {
        return interproceduralCFG().wrap((Local) new JimpleLocal("<<zero>>", NullType.v()));
    }

}

