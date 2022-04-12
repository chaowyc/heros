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
package heros.problems.incremental;

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
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.PrimType;
import soot.Scene;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.UnknownType;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.NewExpr;
import soot.jimple.Ref;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import heros.template.DefaultUpdatableJimpleIFDSTabulationProblem;

@SuppressWarnings("serial")
public class IFDSPossibleTypes extends DefaultUpdatableJimpleIFDSTabulationProblem<UpdatablePossibleType,
        UpdatableInterproceduralCFG<Unit, SootMethod>> {

    public IFDSPossibleTypes(UpdatableInterproceduralCFG<Unit,SootMethod> icfg) {
        super(icfg);
    }

    public FlowFunctions<UpdatableWrapper<Unit>, UpdatablePossibleType, UpdatableWrapper<SootMethod>> createFlowFunctionsFactory() {
        return new FlowFunctions<UpdatableWrapper<Unit>,UpdatablePossibleType,UpdatableWrapper<SootMethod>>() {

            public FlowFunction<UpdatablePossibleType> getNormalFlowFunction
                    (UpdatableWrapper<Unit> src, UpdatableWrapper<Unit> dest) {
                if(src.getContents() instanceof DefinitionStmt) {
                    DefinitionStmt defnStmt = (DefinitionStmt) src.getContents();
                    if(defnStmt.containsInvokeExpr())
                        return Identity.v();
                    final UpdatableWrapper<Value> right = interproceduralCFG().wrap(defnStmt.getRightOp());
                    final UpdatableWrapper<Value> left = interproceduralCFG().wrap(defnStmt.getLeftOp());

                    //won't track primitive-typed variables
                    if(right.getContents().getType() instanceof PrimType)
                        return Identity.v();

                    if(right.getContents() instanceof Constant || right.getContents() instanceof NewExpr) {
                        return new FlowFunction<UpdatablePossibleType>() {
                            public Set<UpdatablePossibleType> computeTargets(UpdatablePossibleType source) {
                                if(source == zeroValue()) {
                                    Set<UpdatablePossibleType> res = new LinkedHashSet<UpdatablePossibleType>();
                                    res.add(new UpdatablePossibleType(left, interproceduralCFG().wrap
                                            (right.getContents().getType())));
                                    res.add(zeroValue());
                                    return res;
                                } else if(source.getValue() instanceof Local && source.getValue().equivTo(left.getContents())) {
                                    //strong update for local variables
                                    return Collections.emptySet();
                                } else {
                                    return Collections.singleton(source);
                                }
                            }
                        };
                    } else if(right instanceof Ref || right instanceof Local) {
                        return new FlowFunction<UpdatablePossibleType>() {
                            public Set<UpdatablePossibleType> computeTargets(final UpdatablePossibleType source) {
                                Value value = source.getValue();
                                if(value instanceof Local && value.equivTo(left.getContents())) {
                                    //strong update for local variables
                                    return Collections.emptySet();
                                } else if(maybeSameLocation(value, right.getContents())) {
                                    return new LinkedHashSet<UpdatablePossibleType>() {{
                                        add(new UpdatablePossibleType(left, interproceduralCFG().wrap(source.getType())));
                                        add(source);
                                    }};
                                } else {
                                    return Collections.singleton(source);
                                }
                            }

                            private boolean maybeSameLocation(Value v1, Value v2) {
                                if(!(v1 instanceof InstanceFieldRef && v2 instanceof InstanceFieldRef) &&
                                        !(v1 instanceof ArrayRef && v2 instanceof ArrayRef)) {
                                    return v1.equivTo(v2);
                                }
                                if(v1 instanceof InstanceFieldRef && v2 instanceof InstanceFieldRef) {
                                    InstanceFieldRef ifr1 = (InstanceFieldRef) v1;
                                    InstanceFieldRef ifr2 = (InstanceFieldRef) v2;
                                    if(!ifr1.getField().getName().equals(ifr2.getField().getName())) return false;

                                    Local base1 = (Local) ifr1.getBase();
                                    Local base2 = (Local) ifr2.getBase();
                                    PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
                                    PointsToSet pts1 = pta.reachingObjects(base1);
                                    PointsToSet pts2 = pta.reachingObjects(base2);
                                    return pts1.hasNonEmptyIntersection(pts2);
                                } else { //v1 instanceof ArrayRef && v2 instanceof ArrayRef
                                    ArrayRef ar1 = (ArrayRef) v1;
                                    ArrayRef ar2 = (ArrayRef) v2;

                                    Local base1 = (Local) ar1.getBase();
                                    Local base2 = (Local) ar2.getBase();
                                    PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
                                    PointsToSet pts1 = pta.reachingObjects(base1);
                                    PointsToSet pts2 = pta.reachingObjects(base2);
                                    return pts1.hasNonEmptyIntersection(pts2);
                                }
                            }
                        };
                    }
                }
                return Identity.v();
            }

            public FlowFunction<UpdatablePossibleType> getCallFlowFunction
                    (final UpdatableWrapper<Unit> src, final UpdatableWrapper<SootMethod> dest) {
                Stmt stmt = (Stmt) src.getContents();
                InvokeExpr ie = stmt.getInvokeExpr();
                final List<UpdatableWrapper<Value>> callArgs = interproceduralCFG().wrap(ie.getArgs());
                final List<UpdatableWrapper<Local>> paramLocals = new ArrayList<UpdatableWrapper<Local>>();
                for (int i = 0; i < dest.getContents().getParameterCount(); i++) {
                    paramLocals.add(interproceduralCFG().wrap
                            (dest.getContents().getActiveBody().getParameterLocal(i)));
                }
                return new FlowFunction<UpdatablePossibleType>() {
                    public Set<UpdatablePossibleType> computeTargets(UpdatablePossibleType source) {
                        if (!dest.getContents().getName().equals("<clinit>")) {
                            Value value = source.getValue();
                            int argIndex = callArgs.indexOf(interproceduralCFG().wrap(value));
                            if(argIndex>-1) {
                                return Collections.singleton(new UpdatablePossibleType
                                        (interproceduralCFG().wrap((Value) paramLocals.get(argIndex).getContents()),
                                                interproceduralCFG().wrap(source.getType())));
                            }
                        }
                        return Collections.emptySet();
                    }
                };
            }

            public FlowFunction<UpdatablePossibleType> getReturnFlowFunction
                    (UpdatableWrapper<Unit> callSite,
                     UpdatableWrapper<SootMethod> callee,
                     UpdatableWrapper<Unit> exitStmt,
                     UpdatableWrapper<Unit> retSite) {
                if (exitStmt.getContents() instanceof ReturnStmt) {
                    ReturnStmt returnStmt = (ReturnStmt) exitStmt.getContents();
                    Value op = returnStmt.getOp();
                    if(op instanceof Local) {
                        if(callSite.getContents() instanceof DefinitionStmt) {
                            DefinitionStmt defnStmt = (DefinitionStmt) callSite.getContents();
                            Value leftOp = defnStmt.getLeftOp();
                            if(leftOp instanceof Local) {
                                final UpdatableWrapper<Value> tgtLocal =
                                        interproceduralCFG().wrap((Value) leftOp);
                                final UpdatableWrapper<Local> retLocal =
                                        interproceduralCFG().wrap((Local) op);
                                return new FlowFunction<UpdatablePossibleType>() {

                                    public Set<UpdatablePossibleType> computeTargets(UpdatablePossibleType source) {
                                        if(source.getValue() == retLocal.getContents())
                                            return Collections.singleton(new UpdatablePossibleType
                                                    (tgtLocal, interproceduralCFG().wrap(source.getType())));
                                        return Collections.emptySet();
                                    }

                                };
                            }
                        }
                    }
                }
                return KillAll.v();
            }

            public FlowFunction<UpdatablePossibleType> getCallToReturnFlowFunction
                    (UpdatableWrapper<Unit> call, UpdatableWrapper<Unit> returnSite) {
                return Identity.v();
            }
        };
    }

    public Set<UpdatableWrapper<Unit>> initialSeeds() {
        return Collections.singleton(interproceduralCFG().wrap
                (Scene.v().getMainMethod().getActiveBody().getUnits().getFirst()));
    }

    public UpdatablePossibleType createZeroValue() {
        return new UpdatablePossibleType(interproceduralCFG().wrap((Value) Jimple.v().newLocal("<dummy>", UnknownType.v())),
                interproceduralCFG().wrap((Type) UnknownType.v()));
    }
}

