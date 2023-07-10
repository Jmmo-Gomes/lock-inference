package org.repla.resources;

import org.repla.code.CodeLabel;
import org.repla.code.Label;
import org.repla.resources.ResourceOperation.OpCode;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.logging.Logger;

public class TwoPhaseLocking extends ResourceAnalysisVisitor {

	public TwoPhaseLocking(Logger logger) {
		super(logger);
	}
	
	@Override
	public boolean visit(ResourceAccessMap map) {

		twoPhaseLocking(this.methodResourceInfo.resourceOperationsMap);

		logger.fine(this.currentMethod.getName() + " [ resource operations map (two phase locking): " + this.methodResourceInfo.resourceOperationsMap + " ]");
		removeTombstones(this.methodResourceInfo.resourceOperationsMap);

		logger.fine(this.currentMethod.getName() + " [ resource operations map (remove tombstones): " + this.methodResourceInfo.resourceOperationsMap + " ]");

		return true;
	}





	/**
	 * Push all the lock release operations to after the last lock operation
	 * @param roMap
	 */
	private void twoPhaseLocking(ResourceOperationsMap roMap) {

		// Compute the label of the last lock
		Label lastLock = new CodeLabel(this.currentMethod, 0);

		for ( Entry<Label, HashSet<ResourceGroup>> entry : roMap.entrySet() ) {
			for (ResourceGroup rgroup : entry.getValue()) {
				for (ResourceOperation rop : rgroup) {
					OpCode op = rop.getOperation();
					if (op == OpCode.UPGRADE || op == OpCode.READ || op == OpCode.EXCLUSIVE)
						lastLock = entry.getKey().after();
				}
			}
		}

		// find groups of RELEASE to push
		Map<ResourceGroup, Entry<Label, HashSet<ResourceGroup>>>  toPush = new HashMap<>();
		for ( Entry<Label, HashSet<ResourceGroup>> entry : roMap.entrySet() ) {

			// before the last lock
			if (entry.getKey().compareTo(lastLock) < 0) {
				for (ResourceGroup rgroup : entry.getValue()) {
					for (ResourceOperation rop : rgroup) {
						if (rop.getOperation() == OpCode.RELEASE) // found a release, mark it
							toPush.put(rgroup, entry);
					}
				}
			}
		}

		//
		for ( Entry<ResourceGroup, Entry<Label, HashSet<ResourceGroup>>> entry : toPush.entrySet() ) {

			HashSet<ResourceGroup> targetGroupSet = entry.getValue().getValue();

			targetGroupSet.remove(entry.getKey());
			if (targetGroupSet.isEmpty())
				roMap.remove(entry.getValue().getKey());
			roMap.put(lastLock, entry.getKey());
		}
	}


	private void removeTombstones(ResourceOperationsMap roMap) {

		var removeMap = new HashSet<Label>();
		for (Entry<Label, HashSet<ResourceGroup>> entry : roMap.entrySet()) {
			var set = entry.getValue();
			var removeSet = new HashSet<ResourceGroup>();
			for (ResourceGroup rg : set) {
				for (ResourceOperation rop : (ResourceGroup) rg.clone()) {
					if (rop.getResource() == null)
						rg.remove(rop);
				}

				if (rg.isEmpty())
					removeSet.add(rg);
			}

			set.removeAll(removeSet);

			if (set.isEmpty())
				removeMap.add(entry.getKey());
		}

		for (Label label : removeMap)
			roMap.remove(label);
	}

}

