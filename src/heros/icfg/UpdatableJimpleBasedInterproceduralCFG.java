package heros.icfg;

import heros.BiDiInterproceduralCFG;
import heros.incremental.AbstractUpdatableInterproceduralCFG;
import heros.incremental.DefaultUpdatableWrapper;
import heros.incremental.UpdatableInterproceduralCFG;
import heros.incremental.UpdatableWrapper;
import heros.solver.Pair;
import heros.util.Utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;
import soot.util.Chain;

import heros.InterproceduralCFG;
import heros.ThreadSafe;
import heros.incremental.SceneDiff;
import heros.incremental.SceneDiff.ClassDiffNode;
import heros.incremental.SceneDiff.DiffType;
import heros.incremental.SceneDiff.MethodDiffNode;
import heros.incremental.SceneDiff.ProgramDiffNode;

/**
 * Default implementation for the {@link InterproceduralCFG} interface.
 * Includes all statements reachable from {@link Scene#getEntryPoints()} through
 * explicit call statements or through calls to {@link Thread#start()}.
 *
 * This class is designed to be thread safe, and subclasses of this class must be designed
 * in a thread-safe way, too.
 */
@ThreadSafe


public class UpdatableJimpleBasedInterproceduralCFG extends AbstractUpdatableInterproceduralCFG<Unit,SootMethod> {

    private final static boolean DEBUG = true;
    private boolean quickDiff = false;

    protected final SceneDiff sceneDiff = new SceneDiff();

    public UpdatableJimpleBasedInterproceduralCFG() {
        super();
        this.sceneDiff.fullBuild();
    }

    public UpdatableJimpleBasedInterproceduralCFG(int capacity) {
        super(capacity);
        this.sceneDiff.fullBuild();
    }

    @Override
    protected JimpleBasedBiDiICFG getBaseCFG() {
        return (JimpleBasedBiDiICFG) super.getBaseCFG();
    }

    @Override
    public void computeCFGChangeset(
            UpdatableInterproceduralCFG<Unit, SootMethod> newCFG,
            Map<UpdatableWrapper<Unit>, List<UpdatableWrapper<Unit>>> expiredEdges,
            Map<UpdatableWrapper<Unit>, List<UpdatableWrapper<Unit>>> newEdges,
            Set<UpdatableWrapper<Unit>> newNodes,
            Set<UpdatableWrapper<Unit>> expiredNodes) {
        if (!(newCFG instanceof UpdatableJimpleBasedInterproceduralCFG))
            throw new RuntimeException("Cannot compare graphs of different type");
        UpdatableJimpleBasedInterproceduralCFG newJimpleCFG =
                (UpdatableJimpleBasedInterproceduralCFG) newCFG;

        long beforeSceneDiff = System.nanoTime();
        System.out.println("Computing code diff...");
        ProgramDiffNode diffRoot = sceneDiff.incrementalBuild();
        if (diffRoot.isEmpty())
            System.out.println("Program is unchanged");
        System.out.println("Incremental build done in "
                + (System.nanoTime() - beforeSceneDiff) / 1E9 + " seconds.");

		/*
		CountingThreadPoolExecutor executor = new CountingThreadPoolExecutor
				(1, Runtime.getRuntime().availableProcessors(),
				30, TimeUnit.SECONDS, new LinkedBlockingQueue<Runnable>());
		*/

        // Check for removed classes. All statements in all methods in all
        // removed classes are automatically expired
        Set<SootClass> changedClasses = new HashSet<SootClass>();
        for (ClassDiffNode cd : diffRoot) {
            changedClasses.add(cd.getNewClass());
            if (cd.getDiffType() == DiffType.REMOVED) {
                if (DEBUG)
                    System.out.println("Removed class: " + cd.getOldClass().getName());
                for (MethodDiffNode md : cd.getMethodDiffs()) {
                    assert md.getDiffType() == DiffType.REMOVED;
                    assert md.getOldMethod() != null;
                    for (Unit u : md.getOldMethod().retrieveActiveBody().getUnits()) {
                        // Since we're running on the old CFG, we must still
                        // have the statement
                        assert this.containsStmt(u);
                        expiredNodes.add(wrap(u));
                    }
                }
            }
            else if (cd.getDiffType() == DiffType.ADDED) {
                if (DEBUG)
                    System.out.println("Added class: " + cd.getNewClass().getName());
                for (MethodDiffNode md : cd.getMethodDiffs()) {
                    assert md.getDiffType() == DiffType.ADDED;
                    assert md.getNewMethod() != null;
                    for (Unit u : md.getNewMethod().retrieveActiveBody().getUnits()) {
                        UpdatableWrapper<Unit> wrapper = wrap(u);
                        newNodes.add(wrapper);
                        assert newJimpleCFG.containsStmt(u);
                    }
                }
            }
            else if (cd.getDiffType() == DiffType.CHANGED) {
                // This class has been changed. All statements in new methods
                // are automatically new.
                for (SootMethod newMethod : cd.getNewClass().getMethods())
                    if (newMethod.isConcrete()) {
                        MethodDiffNode methodDiff = cd.getMethodDiff(newMethod);
                        if (methodDiff != null && methodDiff.getDiffType() == DiffType.ADDED) {
                            if (DEBUG)
                                System.out.println("Added method: " + newMethod.getSignature());
                            for (Unit u : newMethod.retrieveActiveBody().getUnits()) {
                                UpdatableWrapper<Unit> wrapper = wrap(u);
                                newNodes.add(wrapper);
                                assert newJimpleCFG.containsStmt(u);
                            }
                        }
                        else if (methodDiff != null && methodDiff.getDiffType() == DiffType.REMOVED)
                            throw new RuntimeException("Invalid diff mode, new method cannot be removed");
                    }

                // All statements in removed methods are automatically expired.
                for (SootMethod oldMethod : cd.getOldClass().getMethods())
                    if (oldMethod.isConcrete()) {
                        MethodDiffNode methodDiff = cd.getMethodDiff(oldMethod);
                        if (methodDiff != null && methodDiff.getDiffType() == DiffType.REMOVED) {
                            if (DEBUG)
                                System.out.println("Removed method: " + oldMethod.getSignature());
                            for (Unit u : oldMethod.retrieveActiveBody().getUnits()) {
                                assert this.containsStmt(u);
                                expiredNodes.add(wrap(u));
                            }
                        }
                        else if (methodDiff != null && methodDiff.getDiffType() == DiffType.CHANGED) {
                            // This method has been changed
                            if (quickDiff) {
                                quickDiffMethod(newJimpleCFG, oldMethod, methodDiff.getNewMethod(),
                                        expiredEdges, newEdges, newNodes, expiredNodes);
                            }
                            else {
                                boolean reallyChanged = computeMethodChangeset(newJimpleCFG, oldMethod,
                                        methodDiff.getNewMethod(), expiredEdges, newEdges, newNodes, expiredNodes);
                                if (DEBUG && reallyChanged)
                                    System.out.println("Changed method: " + methodDiff.getNewMethod().getSignature());
								/*
								executor.execute(new ComputeMethodChangesetTask(newJimpleCFG, oldMethod,
										methodDiff.getNewMethod(), expiredEdges, newEdges, newNodes, expiredNodes));
								*/
                            }
                        }
                        else if (methodDiff != null && methodDiff.getDiffType() == DiffType.ADDED)
                            throw new RuntimeException("Invalid diff mode, old method cannot be added");
                        else if (methodDiff == null && cd.getNewClass().declaresMethod(oldMethod.getSubSignature())) {
                            // This is an unchanged method in a modified class.
                            // Fix the wrappers
                            updateUnchangedMethodPointers(oldMethod, Scene.v().getMethod(oldMethod.getSignature()));
                        }
                    }
            }
            else
                throw new RuntimeException("Unknown change type: " + cd.getDiffType());
        }

        // Update the wrappers for classes that have not changed
        long beforePointerUpdate = System.nanoTime();
        for (SootClass newClass : newJimpleCFG.getAllClasses()) {
            SootClass oldClass = diffRoot.getOldClassFor(newClass);
            if (oldClass != null && !changedClasses.contains(newClass))
                for (SootMethod newMethod : newClass.getMethods()) {
                    SootMethod oldMethod = diffRoot.getOldMethodFor(newMethod);
                    updateUnchangedMethodPointers(oldMethod, newMethod);
                }
        }
        System.out.println("Unchanged method pointers updated in "
                + (System.nanoTime() - beforePointerUpdate) / 1E9 + " seconds.");

		/*
		// Wait for the method diff threads to finish and shut down the executor
		try {
			executor.awaitCompletion();
		} catch (InterruptedException e) {
			throw new RuntimeException(e);
		}
		executor.shutdown();
		try {
			executor.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
		} catch (InterruptedException e) {
			throw new RuntimeException(e);
		}
		*/
    }

    private void quickDiffMethod(
            UpdatableJimpleBasedInterproceduralCFG newJimpleCFG,
            SootMethod oldMethod,
            SootMethod newMethod,
            Map<UpdatableWrapper<Unit>, List<UpdatableWrapper<Unit>>> expiredEdges,
            Map<UpdatableWrapper<Unit>, List<UpdatableWrapper<Unit>>> newEdges,
            Set<UpdatableWrapper<Unit>> newNodes,
            Set<UpdatableWrapper<Unit>> expiredNodes) {
        long beforeQuickDiff = System.nanoTime();

        List<UpdatableWrapper<Unit>> oldSps = getStartPointsOf(wrap(oldMethod));
        List<UpdatableWrapper<Unit>> newSps = newJimpleCFG.getStartPointsOf(newJimpleCFG.wrap(newMethod));

        // We need to match the references of the start points
        Map<Unit, Unit> refChanges = new HashMap<Unit, Unit>();
        boolean hasSeed = true;
        for (UpdatableWrapper<Unit> spOld : oldSps) {
            boolean found = false;
            for (UpdatableWrapper<Unit> spNew : newSps)
                if (spOld.getContents().toString().equals(spNew.getContents().toString())) {
                    refChanges.put(spOld.getContents(), spNew.getContents());
                    found = true;
                    break;
                }

            // If we cannot match the start points, there is no seed in the
            // current method
            if (!found)
                hasSeed = false;
        }

        for (Unit oldUnit : oldMethod.getActiveBody().getUnits()) {
            UpdatableWrapper<Unit> wOldUnit = wrap(oldUnit);
            if (!hasSeed || !oldSps.contains(wOldUnit))
                expiredNodes.add(wOldUnit);
            for (UpdatableWrapper<Unit> succ : getSuccsOf(wOldUnit))
                Utils.addElementToMapList(expiredEdges, wOldUnit, succ);
        }
        for (Unit newUnit : newMethod.getActiveBody().getUnits()) {
            UpdatableWrapper<Unit> wNewUnit = newJimpleCFG.wrap(newUnit);
            if (!hasSeed || !newSps.contains(wNewUnit))
                newNodes.add(wNewUnit);
            for (UpdatableWrapper<Unit> succ : newJimpleCFG.getSuccsOf(wNewUnit))
                Utils.addElementToMapList(newEdges, wNewUnit, succ);
        }

        for (Entry<Unit, Unit> entry : refChanges.entrySet())
            notifyReferenceChanged(entry.getKey(), entry.getValue());

        System.out.println("Quick diff took " + (System.nanoTime() - beforeQuickDiff) / 1E9
                + " seconds.");
    }

    private class ComputeMethodChangesetTask implements Runnable {

        private final UpdatableJimpleBasedInterproceduralCFG newCFG;
        private final SootMethod oldMethod;
        private final SootMethod newMethod;
        private final Map<UpdatableWrapper<Unit>, List<UpdatableWrapper<Unit>>> expiredEdges;
        private final Map<UpdatableWrapper<Unit>, List<UpdatableWrapper<Unit>>> newEdges;
        private final Set<UpdatableWrapper<Unit>> newNodes;
        private final Set<UpdatableWrapper<Unit>> expiredNodes;

        public ComputeMethodChangesetTask
                (UpdatableJimpleBasedInterproceduralCFG newCFG,
                 SootMethod oldMethod,
                 SootMethod newMethod,
                 Map<UpdatableWrapper<Unit>, List<UpdatableWrapper<Unit>>> expiredEdges,
                 Map<UpdatableWrapper<Unit>, List<UpdatableWrapper<Unit>>> newEdges,
                 Set<UpdatableWrapper<Unit>> newNodes,
                 Set<UpdatableWrapper<Unit>> expiredNodes) {
            this.newCFG = newCFG;
            this.oldMethod = oldMethod;
            this.newMethod = newMethod;
            this.expiredEdges = expiredEdges;
            this.newEdges = newEdges;
            this.newNodes = newNodes;
            this.expiredNodes = expiredNodes;
        }

        @Override
        public void run() {
            boolean reallyChanged = computeMethodChangeset(newCFG, oldMethod,
                    newMethod, expiredEdges, newEdges, newNodes, expiredNodes);
            if (DEBUG && reallyChanged)
                System.out.println("Changed method: " + newMethod.getSignature());
        }

    }

    /**
     * Updates the statement references for an unchanged method. All updateable
     * references to statements in the old method are changed to point to
     * their respective counterparts in the new method.
     * @param oldMethod The old method before the update
     * @param newMethod The new method after the update
     */
    private void updateUnchangedMethodPointers(SootMethod oldMethod, SootMethod newMethod) {
        // If one of the two methods has no body, we cannot match anything
        if (oldMethod == null || !oldMethod.hasActiveBody()
                || newMethod == null || !newMethod.hasActiveBody()
                || oldMethod == newMethod)
            return;

        // As we expect the method to be unchanged, there should be the same
        // number of statements in both the old and the new version
        assert oldMethod.getActiveBody().getUnits().size() ==
                newMethod.getActiveBody().getUnits().size();

        // Update the statement references
        updatePointsFromChain(oldMethod.getActiveBody().getUnits(),
                newMethod.getActiveBody().getUnits());
        updatePointsFromChain(oldMethod.getActiveBody().getLocals(),
                newMethod.getActiveBody().getLocals());
    }

    /**
     * Updates the wrapper references for two equivalent chains. The wrapper for
     * the n-th element in the old chain is changed to point to the n-nth
     * element in the new chain.
     * @param oldChain The old chain
     * @param newChain The new chain
     */
    private <X> void updatePointsFromChain(Chain<X> oldChain, Chain<X> newChain) {
        if (oldChain.isEmpty() || newChain.isEmpty())
            return;

        X uold = oldChain.getFirst();
        X unew = newChain.getFirst();
        while (uold != null && unew != null) {
            assert uold.toString().contains("tmp$") || uold.toString().contains("access$")
                    || uold.toString().equals(unew.toString());
            if (uold instanceof Stmt && unew instanceof Stmt)
                updateReferences((Stmt) uold, (Stmt) unew);
            else
                notifyReferenceChanged(uold, unew);
            uold = oldChain.getSuccOf(uold);
            unew = newChain.getSuccOf(unew);
        }
    }

    @Override
    protected BiDiInterproceduralCFG<Unit, SootMethod> createBaseCFG() {
        return new JimpleBasedBiDiICFG();
    }

    /**
     * Checks whether the given statement is part of this CFG.
     * @param u The statement to check
     * @return True if the given statement is part of this CFG, otherwise
     * false
     */
    public boolean containsStmt(Unit u) {
        return this.getBaseCFG().containsStmt(u);
    }

    /**
     * Checks whether the given statement is part of this CFG.
     * @param u The statement to check
     * @return True if the given statement is part of this CFG, otherwise
     * false
     */
    @Override
    public boolean containsStmt(UpdatableWrapper<Unit> u) {
        return this.getBaseCFG().containsStmt(u.getContents());
    }

    /**
     * Gets all classes that contain methods in this cfg
     * @return All classes that can contain methods in this cfg
     */
    public Collection<SootClass> getAllClasses() {
        return this.getBaseCFG().getAllClasses();
    }

    /**
     * Computes the edge differences between two Soot methods.
     * @param newCFG The new program graph. The current object is assumed to
     * hold the old program graph.
     * @param oldMethod The method before the changes were made
     * @param newMethod The method after the changes have been made
     * @param expiredEdges The map that receives the expired edge targets. If
     * two edges a->b and a->c have expired, the entry (a,(b,c)) will be put in
     * the map.
     * @param newEdges The map that receives the new edge targets.
     * @param newNodes The list that receives all nodes which have been added to
     * the method
     * @param expiredNodes The list that receives all nodes which have been
     * deleted from the method
     * @return True if the two methods were actually different, otherwise false.
     */
    private boolean computeMethodChangeset
    (UpdatableJimpleBasedInterproceduralCFG newCFG,
     SootMethod oldMethod,
     SootMethod newMethod,
     Map<UpdatableWrapper<Unit>, List<UpdatableWrapper<Unit>>> expiredEdges,
     Map<UpdatableWrapper<Unit>, List<UpdatableWrapper<Unit>>> newEdges,
     Set<UpdatableWrapper<Unit>> newNodes,
     Set<UpdatableWrapper<Unit>> expiredNodes) {

        assert newCFG != null;
        assert oldMethod != null;
        assert newMethod != null;
        assert expiredEdges != null;
        assert newEdges != null;
        assert newNodes != null;

        // Map the locals that have been retained
        for (Local oldLocal : oldMethod.getActiveBody().getLocals()) {
            for (Local newLocal : newMethod.getActiveBody().getLocals())
                if (oldLocal.getName().equals(newLocal.getName())
                        && oldLocal.getType().toString().equals(newLocal.getType().toString())) {
                    notifyReferenceChanged(oldLocal, newLocal);
                    break;
                }
        }

        // Delay reference changes until the end for not having to cope with
        // changing references inside our analysis
        Map<Unit, Unit> refChanges = new HashMap<Unit, Unit>();

        // For all entry points of the new method, try to find the corresponding
        // statements in the old method. If we don't a corresponding statement,
        // we record a NULL value.
        boolean reallyChanged = false;
        List<Pair<UpdatableWrapper<Unit>,UpdatableWrapper<Unit>>> workQueue =
                new ArrayList<Pair<UpdatableWrapper<Unit>,UpdatableWrapper<Unit>>>();
        Set<UpdatableWrapper<Unit>> doneList = new HashSet<UpdatableWrapper<Unit>>(10000);
        for (UpdatableWrapper<Unit> spNew : newCFG.getStartPointsOf
                (new DefaultUpdatableWrapper<SootMethod>(newMethod))) {
            UpdatableWrapper<Unit> spOld = findStatement
                    (new DefaultUpdatableWrapper<SootMethod>(oldMethod), spNew);
            workQueue.add(new Pair<UpdatableWrapper<Unit>,UpdatableWrapper<Unit>>(spNew, spOld));
            if (spOld == null) {
                assert newCFG.containsStmt(spNew);
                newNodes.add(spNew);
            }
            else
                refChanges.put(spOld.getContents(), spNew.getContents());
        }

        while (!workQueue.isEmpty()) {
            // Dequeue the current element and make sure we don't run in circles
            Pair<UpdatableWrapper<Unit>,UpdatableWrapper<Unit>> ns = workQueue.remove(0);
            UpdatableWrapper<Unit> newStmt = ns.getO1();
            UpdatableWrapper<Unit> oldStmt = ns.getO2();
            if (!doneList.add(newStmt))
                continue;

            // If the current point is unreachable, we skip the remainder of the method
            assert newCFG.containsStmt(newStmt.getContents());

            // Find the outgoing edges and check whether they are new
            boolean isNewStmt = newNodes.contains(newStmt);
            for (UpdatableWrapper<Unit> newSucc : newCFG.getSuccsOf(newStmt)) {
                UpdatableWrapper<Unit> oldSucc = oldStmt == null ? null : findStatement(getSuccsOf(oldStmt), newSucc);
                if (oldSucc == null || !getSuccsOf(oldStmt).contains(oldSucc) || isNewStmt) {
                    Utils.addElementToMapList(newEdges, oldStmt == null ? newStmt : oldStmt,
                            oldSucc == null ? newSucc : oldSucc);
                    reallyChanged = true;
                }
                if (oldSucc == null)
                    newNodes.add(newSucc);
                workQueue.add(new Pair<UpdatableWrapper<Unit>,UpdatableWrapper<Unit>>
                        (newSucc, oldSucc == null ? oldStmt : oldSucc));

                if (oldSucc != null)
                    refChanges.put(oldSucc.getContents(), newSucc.getContents());
            }
        }

        // For all entry points of the old method, check whether we can reach a
        // statement that is no longer present in the new method.
        doneList.clear();
        for (UpdatableWrapper<Unit> spOld : getStartPointsOf(new DefaultUpdatableWrapper<SootMethod>(oldMethod))) {
            UpdatableWrapper<Unit> spNew = newCFG.findStatement(new DefaultUpdatableWrapper<SootMethod>(newMethod), spOld);
            workQueue.add(new Pair<UpdatableWrapper<Unit>,UpdatableWrapper<Unit>>(spNew, spOld));
            if (spNew == null)
                expiredNodes.add(spOld);
        }

        while (!workQueue.isEmpty()) {
            // Dequeue the current element and make sure we don't run in circles
            Pair<UpdatableWrapper<Unit>,UpdatableWrapper<Unit>> ns = workQueue.remove(0);
            UpdatableWrapper<Unit> newStmt = ns.getO1();
            UpdatableWrapper<Unit> oldStmt = ns.getO2();
            if (!doneList.add(oldStmt))
                continue;

            // If the current point is unreachable, we skip the remainder of the method
            assert this.containsStmt(oldStmt.getContents());

            // Find the outgoing edges and check whether they are expired
            boolean isExpiredStmt = expiredNodes.contains(oldStmt);
            for (UpdatableWrapper<Unit> oldSucc : getSuccsOf(oldStmt)) {
                UpdatableWrapper<Unit> newSucc = newStmt == null ? null : newCFG.findStatement
                        (newCFG.getSuccsOf(newStmt), oldSucc);
                if (newSucc == null || !newCFG.getSuccsOf(newStmt).contains(newSucc) || isExpiredStmt) {
                    Utils.addElementToMapList(expiredEdges, oldStmt, oldSucc);
                    reallyChanged = true;
                }
                if (newSucc == null) {
                    expiredNodes.add(oldSucc);
                    assert this.containsStmt(oldSucc);
                }
                workQueue.add(new Pair<UpdatableWrapper<Unit>,UpdatableWrapper<Unit>>
                        (newSucc == null ? newStmt : newSucc, oldSucc));

                if (newSucc != null)
                    refChanges.put(oldSucc.getContents(), newSucc.getContents());
            }
        }

        // Make sure that every statement is either added or removed or remapped
        if (DEBUG) {
            doneList.clear();
            List<UpdatableWrapper<Unit>> checkQueue = new ArrayList<UpdatableWrapper<Unit>>();
            checkQueue.addAll(this.getStartPointsOf(wrap(oldMethod)));
            while (!checkQueue.isEmpty()) {
                UpdatableWrapper<Unit> curUnit = checkQueue.remove(0);
                if (!doneList.add(curUnit))
                    continue;
                checkQueue.addAll(this.getSuccsOf(curUnit));
                assert expiredNodes.contains(curUnit)
                        || newNodes.contains(curUnit)
                        || refChanges.containsKey(curUnit.getContents());
            }
        }

        for (Entry<Unit,Unit> entry : refChanges.entrySet())
            updateReferences(entry.getKey(), entry.getValue());
        return reallyChanged;
    }

    private void updateReferences(Unit oldUnit, Unit newUnit) {
        notifyReferenceChanged(oldUnit, newUnit);

        Stmt oldStmt = (Stmt) oldUnit;
        Stmt newStmt = (Stmt) newUnit;
        if (oldStmt.containsFieldRef())
            notifyReferenceChanged(oldStmt.getFieldRef(), newStmt.getFieldRef());
        if (oldStmt.containsArrayRef())
            notifyReferenceChanged(oldStmt.getArrayRef(), newStmt.getArrayRef());

        assert this.containsStmt(oldUnit);
//		assert newCFG.containsStmt(newUnit);
    }

    private UpdatableWrapper<Unit> findStatement
            (UpdatableWrapper<SootMethod> oldMethod,
             UpdatableWrapper<Unit> newStmt) {
        return findStatement(getStartPointsOf(oldMethod), newStmt);
    }

    private UpdatableWrapper<Unit> findStatement
            (Iterable<UpdatableWrapper<Unit>> oldMethod,
             UpdatableWrapper<Unit> newStmt) {
        List<UpdatableWrapper<Unit>> doneList = new ArrayList<UpdatableWrapper<Unit>>();
        return findStatement(oldMethod, newStmt, doneList);
    }

    private UpdatableWrapper<Unit> findStatement
            (Iterable<UpdatableWrapper<Unit>> oldMethod,
             UpdatableWrapper<Unit> newStmt,
             List<UpdatableWrapper<Unit>> doneList) {
        List<UpdatableWrapper<Unit>> workList = new ArrayList<UpdatableWrapper<Unit>>();
        for (UpdatableWrapper<Unit> u : oldMethod)
            workList.add(u);

        while (!workList.isEmpty()) {
            UpdatableWrapper<Unit> sp = workList.remove(0);
            if (doneList.contains(sp))
                continue;
            doneList.add(sp);

            if (sp == newStmt || sp.equals(newStmt) || sp.toString().equals
                    (newStmt.toString()))
                return sp;
            workList.addAll(getSuccsOf(sp));
        }
        return null;
    }

    @Override
    public UpdatableWrapper<Unit> getLoopStartPointFor(UpdatableWrapper<Unit> stmt) {
        Unit u = getBaseCFG().getLoopStartPointFor(stmt.getContents());
        return u == null ? null : wrap(u);
    }

    @Override
    public Set<UpdatableWrapper<Unit>> getExitNodesForReturnSite(UpdatableWrapper<Unit> stmt) {
        return this.wrap(getBaseCFG().getExitNodesForReturnSite(stmt.getContents()));
    }

    @Override
    public UpdatableWrapper<SootMethod> getMethodOf(UpdatableWrapper<Unit> n) {
        UpdatableWrapper<SootMethod> method = super.getMethodOf(n);
        assert this.sceneDiff.containsReachableMethod(method.getContents());
        return method;
    }

    /**
     * Sets whether quick diffing shall be used. Quick diffing only scans for
     * structural changes when updating the CFG and then exchanges all
     * statements in methods that are not preserved as-is.
     * @param quickDiff True if quick diffing shall be enabled, otherwise false.
     */
    public void setQuickDiff(boolean quickDiff) {
        this.quickDiff = quickDiff;
    }

    /**
     * Gets whether quick diffing is used.  Quick diffing only scans for
     * structural changes when updating the CFG and then exchanges all
     * statements in methods that are not preserved as-is.
     * @return True if quick diffing is enabled, otherwise false.
     */
    public boolean getQuickDiff() {
        return this.quickDiff;
    }

}

