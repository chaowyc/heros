package heros.problems.incremental;


import heros.FlowFunction;
import heros.FlowFunctions;
import heros.flowfunc.Identity;
import heros.flowfunc.KillAll;
import heros.incremental.UpdatableInterproceduralCFG;
import heros.incremental.UpdatableWrapper;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ExecutionException;

import soot.EquivalentValue;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;
import heros.template.DefaultUpdatableJimpleIFDSTabulationProblem;
import soot.toolkits.scalar.Pair;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;

public class IFDSReachingDefinitions extends DefaultUpdatableJimpleIFDSTabulationProblem
        <UpdatableReachingDefinition, UpdatableInterproceduralCFG<Unit, SootMethod>> {

    private static final UpdatableReachingDefinition zeroValue = UpdatableReachingDefinition.zero;
    private final LoadingCache<Pair<UpdatableWrapper<Value>, Set<UpdatableWrapper<DefinitionStmt>>>,
            UpdatableReachingDefinition> wrapperObjects;

    public IFDSReachingDefinitions(final UpdatableInterproceduralCFG<Unit, SootMethod> icfg) {
        super(icfg);

        CacheBuilder<Object, Object> cb = CacheBuilder.newBuilder().concurrencyLevel
                (Runtime.getRuntime().availableProcessors()).initialCapacity(100000); //.weakKeys();
        this.wrapperObjects = cb.build(new CacheLoader<Pair<UpdatableWrapper<Value>,
                Set<UpdatableWrapper<DefinitionStmt>>>, UpdatableReachingDefinition>() {

            @Override
            public UpdatableReachingDefinition load
                    (Pair<UpdatableWrapper<Value>, Set<UpdatableWrapper<DefinitionStmt>>> key) throws Exception {
                UpdatableReachingDefinition urd = new UpdatableReachingDefinition(key.getO1(), key.getO2());
                return urd;
            }

        });
    }

    private UpdatableReachingDefinition createReachingDefinition(Value value, Set<DefinitionStmt> definitions) {
        UpdatableWrapper<Value> wrappedValue = this.interproceduralCFG().wrap(value);
        Set<UpdatableWrapper<DefinitionStmt>> wrappedDefs = this.interproceduralCFG().wrap(definitions);
        Pair<UpdatableWrapper<Value>, Set<UpdatableWrapper<DefinitionStmt>>> pair =
                new Pair<UpdatableWrapper<Value>, Set<UpdatableWrapper<DefinitionStmt>>>(wrappedValue, wrappedDefs);

        try {
            return this.wrapperObjects.get(pair);
        } catch (ExecutionException e) {
            System.err.println("Could not wrap object");
            e.printStackTrace();
            return null;
        }
    }

    @Override
    public FlowFunctions<UpdatableWrapper<Unit>, UpdatableReachingDefinition, UpdatableWrapper<SootMethod>> createFlowFunctionsFactory() {
        return new FlowFunctions<UpdatableWrapper<Unit>, UpdatableReachingDefinition, UpdatableWrapper<SootMethod>>() {

            @Override
            public FlowFunction<UpdatableReachingDefinition> getNormalFlowFunction
                    (final UpdatableWrapper<Unit> curr, UpdatableWrapper<Unit> succ) {
                if (curr.getContents() instanceof DefinitionStmt) {
                    final UpdatableWrapper<DefinitionStmt> assignment = interproceduralCFG().wrap
                            ((DefinitionStmt) curr.getContents());

                    return new FlowFunction<UpdatableReachingDefinition>() {
                        @Override
                        public Set<UpdatableReachingDefinition> computeTargets(UpdatableReachingDefinition source) {
                            if (!source.equals(zeroValue())) {
                                UpdatableWrapper<Value> sourceLocal = interproceduralCFG().wrap(source.getContents().getO1());
                                UpdatableWrapper<Value> assignLocal = interproceduralCFG().wrap(assignment.getContents().getLeftOp());
                                if (sourceLocal.equals(assignLocal)) {
                                    return Collections.emptySet();
                                }
                                return Collections.singleton(source);
                            } else {
                                return Collections.singleton(createReachingDefinition(assignment.getContents().getLeftOp(),
                                        Collections.<DefinitionStmt> singleton(assignment.getContents())));
                            }
                        }
                    };
                }

                return Identity.v();
            }

            @Override
            public FlowFunction<UpdatableReachingDefinition> getCallFlowFunction
                    (UpdatableWrapper<Unit> callStmt,
                     final UpdatableWrapper<SootMethod> destinationMethod) {
                Stmt stmt = (Stmt) callStmt.getContents();
                InvokeExpr invokeExpr = stmt.getInvokeExpr();
                final List<UpdatableWrapper<Value>> args = interproceduralCFG().wrap(invokeExpr.getArgs());

                return new FlowFunction<UpdatableReachingDefinition>() {

                    @Override
                    public Set<UpdatableReachingDefinition> computeTargets(UpdatableReachingDefinition source) {
                        // Dot not map parameters for <clinit> edges
                        if (destinationMethod.getContents().getName().equals("<clinit>"))
                            return Collections.emptySet();

                        UpdatableWrapper<Value> value = interproceduralCFG().wrap(source.getValue());
                        if(args.contains(value)) {
                            int paramIndex = args.indexOf(value);
                            UpdatableReachingDefinition pair = createReachingDefinition
                                    (new EquivalentValue(Jimple.v().newParameterRef
                                                    (destinationMethod.getContents().getParameterType(paramIndex), paramIndex)),
                                            source.getContents().getO2());
                            return Collections.singleton(pair);
                        }

                        return Collections.emptySet();
                    }
                };
            }

            @Override
            public FlowFunction<UpdatableReachingDefinition> getReturnFlowFunction
                    (final UpdatableWrapper<Unit> callSite,
                     UpdatableWrapper<SootMethod> calleeMethod,
                     final UpdatableWrapper<Unit> exitStmt,
                     UpdatableWrapper<Unit> returnSite) {
                if (!(callSite.getContents() instanceof DefinitionStmt))
                    return KillAll.v();

                if (exitStmt.getContents() instanceof ReturnVoidStmt)
                    return KillAll.v();

                return new FlowFunction<UpdatableReachingDefinition>() {

                    @Override
                    public Set<UpdatableReachingDefinition> computeTargets(UpdatableReachingDefinition source) {
                        assert source.getContents() != null;
                        if (exitStmt.getContents() instanceof ReturnStmt) {
                            ReturnStmt returnStmt = (ReturnStmt) exitStmt.getContents();
                            if (returnStmt.getOp().equivTo(source.getContents().getO1())) {
                                DefinitionStmt definitionStmt = (DefinitionStmt) callSite.getContents();
                                UpdatableReachingDefinition pair = createReachingDefinition
                                        (definitionStmt.getLeftOp(), source.getContents().getO2());
                                return Collections.singleton(pair);
                            }
                        }
                        return Collections.emptySet();
                    }
                };
            }

            @Override
            public FlowFunction<UpdatableReachingDefinition> getCallToReturnFlowFunction
                    (UpdatableWrapper<Unit> callSite, UpdatableWrapper<Unit> returnSite) {
                if (!(callSite.getContents() instanceof DefinitionStmt))
                    return Identity.v();

                final UpdatableWrapper<DefinitionStmt> definitionStmt = interproceduralCFG().wrap
                        ((DefinitionStmt) callSite.getContents());
                return new FlowFunction<UpdatableReachingDefinition>() {

                    @Override
                    public Set<UpdatableReachingDefinition> computeTargets(UpdatableReachingDefinition source) {
                        if(source.getContents().getO1().equivTo(definitionStmt.getContents().getLeftOp())) {
                            return Collections.emptySet();
                        } else {
                            return Collections.singleton(source);
                        }
                    }
                };
            }
        };
    }

    @Override
    public Set<UpdatableWrapper<Unit>> initialSeeds() {
        return Collections.singleton(this.interproceduralCFG().wrap
                (Scene.v().getMainMethod().getActiveBody().getUnits().getFirst()));
    }

    public UpdatableReachingDefinition createZeroValue() {
        return zeroValue;
    }

}


