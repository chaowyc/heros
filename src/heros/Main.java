package heros;

import java.io.File;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import heros.icfg.UpdatableJimpleBasedInterproceduralCFG;
import heros.incremental.UpdatableInterproceduralCFG;
import heros.problems.incremental.IFDSReachingDefinitions;
import heros.problems.incremental.UpdatableReachingDefinition;
import heros.solver.IFDSSolverInc;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.PackManager;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootMethod;
import soot.Transform;
import soot.Unit;
import soot.jimple.AssignStmt;
import soot.jimple.Jimple;
import soot.jimple.StaticInvokeExpr;
import heros.problems.IFDSLocalInfoFlow;
import heros.solver.IFDSSolver;
import heros.icfg.JimpleBasedInterproceduralCFG;
import heros.incremental.UpdatableWrapper;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.ReachableMethods;

public class Main {

    /**
     * @param args
     */
    public static void main(String[] args) {
        soot.G.reset();
        String className = "org.junit.runner.JUnitCore";
        PackManager.v().getPack("wjtp").add(new Transform("wjtp.ifds", new SceneTransformer() {
            protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
                Scene.v().getSootClass(className).setApplicationClass();
                long timeBefore = System.nanoTime();
                System.out.println("Running IFDS on initial CFG...");

                long nanoBeforeCFG = System.nanoTime();
                UpdatableJimpleBasedInterproceduralCFG icfgInc = new UpdatableJimpleBasedInterproceduralCFG();
                icfgInc.setQuickDiff(true);
                System.out.println("ICFG created in " + (System.nanoTime() - nanoBeforeCFG) / 1E9 + " seconds.");

                IFDSTabulationProblem<UpdatableWrapper<Unit>, UpdatableReachingDefinition, UpdatableWrapper<SootMethod>,
                        UpdatableInterproceduralCFG<Unit, SootMethod>> problemInc =
                        new IFDSReachingDefinitions(icfgInc);

                IFDSSolverInc<UpdatableWrapper<Unit>,UpdatableReachingDefinition,UpdatableWrapper<SootMethod>,
                        UpdatableInterproceduralCFG<Unit,SootMethod>> solverInc =
                        new IFDSSolverInc<UpdatableWrapper<Unit>,UpdatableReachingDefinition,UpdatableWrapper<SootMethod>,
                                UpdatableInterproceduralCFG<Unit,SootMethod>>(problemInc);

                long beforeSolver = System.nanoTime();
                System.out.println("Running solver...");
                solverInc.solve();
                System.out.println("Solver done in " + ((System.nanoTime() - beforeSolver) / 1E9) + " seconds.");

//                SootMethod meth = Scene.v().getMainClass().getMethodByName("runMainAndExit");
//                UpdatableWrapper<Unit> ret = icfg.wrap(meth.getActiveBody().getUnits().getPredOf
//                        (meth.getActiveBody().getUnits().getLast()));
//                Set<UpdatableReachingDefinition> results = solver.ifdsResultsAt(ret);
//                checkInitialLeaks(results);

                System.out.println("Time elapsed: " + ((double) (System.nanoTime() - timeBefore)) / 1E9);
            }
        }));

        String os = System.getProperty("os.name");
        String cpSep = ":";
        if (os.contains("Windows"))
            cpSep = ";";

        String udir = System.getProperty("user.dir");
        String sootcp = udir + File.separator + "test/junit-4.10.jar" + cpSep
                + "/usr/lib/jvm/java-8-openjdk-amd64/jre/lib/rt.jar" + cpSep
                + "/usr/lib/jvm/java-8-openjdk-amd64/jre/lib/jce.jar";

        System.out.println("Soot classpath: " + sootcp);
        soot.Main.v().run(new String[] {
                "-W",
                "-main-class", className,
                "-process-path", udir + File.separator + "test",
                "-src-prec", "java",
                "-allow-phantom-refs",
//				"-pp",
//				"-no-bodies-for-excluded",
                "-exclude", "java",
                "-exclude", "javax",
                "-cp", sootcp,
                "-output-format", "none",
                "-p", "jb", "use-original-names:true",
                "-p", "cg.spark", "on",
//				"-p", "cg.spark", "verbose:true",
                /*"-app",*/ className } );
    }

}
