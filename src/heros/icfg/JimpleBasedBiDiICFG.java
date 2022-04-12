package heros.icfg;

import heros.BiDiInterproceduralCFG;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import soot.Body;
import soot.SootMethod;
import soot.Unit;
import soot.toolkits.graph.DirectedGraph;

/**
 * A {@link JimpleBasedInterproceduralCFG} which also supports the computation
 * of predecessors.
 */
public class JimpleBasedBiDiICFG extends JimpleBasedInterproceduralCFG implements BiDiInterproceduralCFG<Unit,SootMethod> {

    @Override
    public List<Unit> getPredsOf(Unit u) {
        Body body = unitToOwner.get(u);
        DirectedGraph<Unit> unitGraph = getOrCreateUnitGraph(body);
        return unitGraph.getPredsOf(u);
    }

    /**
     * Gets all exit nodes that can transfer the control flow to the given
     * return site.
     * @param stmt The return site for which to get the exit nodes
     * @return The set of exit nodes that transfer the control flow to the
     * given return site.
     */
    public Set<Unit> getExitNodesForReturnSite(Unit stmt) {
        List<Unit> preds = this.getPredsOf(stmt);
        Set<Unit> exitNodes = new HashSet<Unit>(preds.size() * 2);
        for (Unit pred : preds)
            for (SootMethod sm : this.getCalleesOfCallAt(pred))
                exitNodes.addAll(getEndPointsOf(sm));
        return exitNodes;
    }

}