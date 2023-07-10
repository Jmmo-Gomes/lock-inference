package org.repla.resources;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.logging.Logger;

/**
 * if forall accesses of r exists r' that encloses r, then r can be removed
 */
public class ResourceOperationSubsumption extends ResourceAnalysisVisitor {

	Map <Resource, HashSet<Resource>> tested = new HashMap<>();
	                                                                          ;
	public ResourceOperationSubsumption(Logger logger) {
		super(logger);
	}

	@Override
	public boolean visit(ResourceAccessMap raMap) {

		Map<FieldResource, FieldResource> candidates = new HashMap<>();
		for (Resource r1 : raMap.keySet()) {
			if (r1.isAField() && r1.getNature().isAtomic()) {

				var testedSet = tested.get(r1);
				if (testedSet == null) {
					testedSet = new HashSet<>();
					tested.put(r1, testedSet);
				}

				for (Resource r2 : raMap.keySet()) {
					if (r2.isAField()
							&& r1 != r2
							&& r2.getNature().isAtomic()
							&& !testedSet.contains(r2)
							&& r1.getMethods().containsAll(r2.getMethods())) {

						candidates.put((FieldResource) r2, (FieldResource) r1);
						testedSet.add(r2);
					}
				}
			}
		}

		Map<FieldResource, HashSet<FieldResource>> guards = new HashMap<>();
		for (Map.Entry<FieldResource, FieldResource> entry : candidates.entrySet()) {
			var subsumed = entry.getKey();
			var dominant = entry.getValue();

			var set = guards.get(subsumed);
			if ((set == null || !set.contains(dominant)) && subsumes(dominant, subsumed))  {
				subsumed.setSubsubmedBy(dominant);
				set = guards.get(dominant);
				if (set == null) {
					set = new HashSet<>();
					guards.put(dominant, set);
				}
				set.add(subsumed);

				// Remove the accesses from the access maps
				for (var minfo: subsumed.getMethods()) 
					minfo.getResourceAccessMap().remove(subsumed);
			}
		}

		return true;
	}

	/**
	 *
	 * @param dominant
	 * @param resource
	 * @return True if dominant subsumes resource, false, otherwise
	 */
	private boolean subsumes(FieldResource dominant, FieldResource resource) {

		for (var minfo: resource.getMethods()) {
			var resourceRA = minfo.getResourceAccessMap().get(resource);
			var dominantRA = minfo.getResourceAccessMap().get(dominant);

			if (resourceRA.hasReadAccess()) {
				// a read access is not included in the read or write accesses of dominant
				if ((dominantRA.getFirstRead().compareTo(resourceRA.getFirstRead()) > 0
						&& dominantRA.getFirstRead().compareTo(resourceRA.getFirstWrite()) > 0)
					|| (dominantRA.getLastRead().compareTo(resourceRA.getLastRead()) < 0
						&& dominantRA.getLastRead().compareTo(resourceRA.getLastWrite()) < 0))

					return false;
			}
			if (resourceRA.hasWriteAccess()) {
				// a write access is not included in the write accesses of dominant
				if (dominantRA.getFirstWrite().compareTo(resourceRA.getFirstWrite()) > 0
					|| dominantRA.getLastWrite().compareTo(resourceRA.getLastWrite()) < 0)

					return false;
			}
		}

		return true;
	}
}
