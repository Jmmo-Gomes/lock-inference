package org.repla.resources;

import org.repla.ReplaException;
import org.repla.atomis.atomicity.Nature;
import org.repla.code.Label;
import org.repla.resources.ResourceOperation.OpCode;
import org.repla.types.Method;
import org.repla.types.Type;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.logging.Logger;

/**
 * Stage that groups object parameters of compatible types.
 * It is executed locally by each method.
 *
 *
 */
public class ParameterResourceOperationGrouping extends ResourceAnalysisVisitor {

	/**
	 * The parameters of the method
	 */
	private final Set<Resource> parameters = new HashSet<>();

	public ParameterResourceOperationGrouping(Logger logger) {
		super(logger);
	}

	@Override
	public boolean visit(Method method) throws ReplaException {
		// Clear the parameters set before processing a method
		parameters.clear();
		return super.visit(method);
	}

	@Override
	public boolean visit(ResourceOperationsMap map) {

		// Collect the parameters
		for (Map.Entry<Label, HashSet<ResourceGroup>> entry : map.entrySet()) {
			if (entry.getKey().isParameter()) {
				for (ResourceGroup rgroup : entry.getValue())
					parameters.addAll(rgroup.getResources());
				break; // there is only one entry with parameters
			}
		}

		if (parameters.isEmpty())
			return true;

		// Set of parameters that hava been handled wrt to the current (r1ROResource)
		Set<Resource> handled = new HashSet<>();

		ResourceOperationsMap clonedMap = (ResourceOperationsMap) map.clone();

		for (Map.Entry<Label, HashSet<ResourceGroup>> r1 : clonedMap.entrySet()) {
			final Label r1Label = r1.getKey();

			for (ResourceGroup r1Group : r1.getValue()) { // for each group
				for (ResourceOperation r1RO : ((ResourceGroup) r1Group.clone())) {
					final OpCode r1ROCode = r1RO.getOperation();
					final Resource r1ROResource = r1RO.getResource();

					if ((r1ROCode == OpCode.EXCLUSIVE || r1ROCode == OpCode.UPGRADE
									|| r1ROCode == OpCode.SHARED_BEFORE_EXCLUSIVE || r1ROCode == OpCode.READ)
							&& this.parameters.contains(r1ROResource)
							&& map.containsKey(r1Label)) { // it is still there

						handled.clear();
						handled.add(r1ROResource);
						var groupsAhead = clonedMap.tailMap(r1Label, false).entrySet();
							checkGrouping(map, handled, r1Group, r1ROCode, r1ROResource, groupsAhead);
					}
				}
			}
		}

		return true;
	}

	private void checkGrouping(ResourceOperationsMap map, Set<Resource> handled, ResourceGroup r1Group, OpCode r1ROCode,
							   Resource r1ROResource, Set<Map.Entry<Label, HashSet<ResourceGroup>>> groupsAhead) {

		for (Map.Entry<Label, HashSet<ResourceGroup>> r2 : groupsAhead) {
		final Label r2Label = r2.getKey();

		for (ResourceGroup r2Group : r2.getValue()) { // for each group
			for (ResourceOperation r2RO : ((ResourceGroup) r2Group.clone())) {
				final OpCode r2ROCode = r2RO.getOperation();
				final Resource r2ROResource = r2RO.getResource();

				if (!handled.contains(r2ROResource)
						&& conflict(r1ROCode, r2ROCode)
						&& conflict(r1ROResource.getType(), r1ROResource.getNature(),
						r2ROResource.getType(), r2ROResource.getNature())
						&& this.parameters.contains(r2ROResource)
						&& map.containsKey(r2Label)) {

					handled.add(r2ROResource);
					var originalR2RO = r2RO;
					if (r2ROCode == OpCode.UPGRADE) {
						// check if any of the groups ahead contain a SHARE_BEFORE_EXCLUSIVE for the same resource
						// If not,  it is before, we keep the UPGRADE
						// If so, remove SBE and replace UPGRADE by an EXCLUSIVE

						boolean foundSBE = false;

						outerLoop:
						for (Map.Entry<Label, HashSet<ResourceGroup>> rAhead : groupsAhead) {
							for (ResourceGroup groupAhead : rAhead.getValue()) {
								var sbe = groupAhead.get(OpCode.SHARED_BEFORE_EXCLUSIVE, r2ROResource);
								if (sbe != null) {
									remove(rAhead.getKey(), groupAhead, sbe, map);
									foundSBE = true;
									break outerLoop;
								}
							}
						}

						if (foundSBE)
							r2RO = new ResourceOperation(OpCode.EXCLUSIVE, r2ROResource);

					}

					r1Group.add(r2RO);
					remove(r2Label, r2Group, originalR2RO, map);

					checkGrouping(map, handled, r1Group, r2RO.getOperation(), r2ROResource, groupsAhead);
				}
			}
		}
		}
	}

	/**
	 * Remove operation from group and, if the group becomes empty, remove it from the ResourceOperationsMap
	 * @param label
	 * @param group
	 * @param rop
	 * @param map
	 */
	private void remove(Label label, ResourceGroup group, ResourceOperation rop, ResourceOperationsMap map) {

		group.remove(rop);

		if (group.isEmpty()) {
			Set<ResourceGroup> resourceGroups = map.get(label);
			if (resourceGroups.size() == 1)
				map.remove(label);
			else
				resourceGroups.remove(group);
		}

	}


	private boolean conflict(OpCode first, OpCode second) {

		if ( (first == OpCode.RELEASE || first == OpCode.DOWNGRADE) ||
			 (second == OpCode.RELEASE || second == OpCode.DOWNGRADE) )
					return false;

		return (first == OpCode.EXCLUSIVE || first == OpCode.UPGRADE)
				|| (second == OpCode.EXCLUSIVE || second == OpCode.UPGRADE);
	}

	/**
	 * Check when two types conflict.
	 *
	 * @param type1 Type of the first type
	 * @param nature1 Nature of the first type
	 * @param type2 Type of the second type
	 * @param nature2 Nature of the second type
	 * @return True or false
	 */
	private boolean conflict(Type type1, Nature nature1, Type type2, Nature nature2) {
		return (nature1 == nature2 && (type1.isSubtypeOf(type2) || type2.isSubtypeOf(type1)));
	}

}