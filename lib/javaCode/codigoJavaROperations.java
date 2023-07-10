package org.repla.resources;

import org.repla.code.Label;
import org.repla.types.Visitable;

import java.util.HashSet;
import java.util.TreeMap;


/**
 * Map of labels into sets of resource operations.
 * 
 * For instance  label1 -> Release r1, ...
 * @author herve
 *
 */
public class ResourceOperationsMap 
	extends TreeMap<Label, HashSet<ResourceGroup>>
	implements Visitable<ResourceAnalysisVisitor> {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	@Override
	public void accept(ResourceAnalysisVisitor visitor) {
		visitor.visit(this);
	}
	
	//@Override

	public void put(Label key, ResourceOperation rop) {

		HashSet<ResourceGroup> set = get(key);

		if (set == null) {
			set = new HashSet<>();
			put(key, set);
		}

		ResourceGroup rgroup = new ResourceGroup();
		rgroup.add(rop);
		set.add(rgroup);
	}

	public void put(Label key, ResourceGroup rgroup) {
				
		HashSet<ResourceGroup> set = get(key);
		
		if (set == null) {
			set = new HashSet<>();
			put(key, set);
		}

		set.add(rgroup);
	}

}









