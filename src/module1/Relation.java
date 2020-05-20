/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package module1;

import java.util.HashSet;
import java.util.Set;

/**
 *
 * @author asus
 */
public final class Relation {
    
   
   
	private final Set<Attribute> attrs;
	private final Set<FuncDep> fds;

	/**
	 * The default constructors
	 * @param attrs a set of attributes
	 * @param fds a set of FD's
	 */
	public Relation(Set<Attribute> attrs, Set<FuncDep> fds) {
		this.attrs = new HashSet<>(attrs);
		this.fds = new HashSet<>(fds);
                //this.keys = new HashSet<>(keys);
	}
	
	/**
	 * Quickly construct a {@code Relation} object with two formatted strings, one for attributes and another for FD's
	 * @param names a string formatted as the following example: "name, application, date, gender"
	 * @param exprs a string formatted as the following example: "{@code a, b --> c; d --> e, f}"
	 */
	public Relation(String names, String exprs){
		this.attrs = Attribute.getSet(names);
		this.fds = FuncDep.getSet(exprs);
	}
	
	/**
	 * Quickly construct a {@code Relation} object with two string arrays
	 * @param names each element will be used as the {@code name} of an {@code Attribute} object
	 * @param exprs each element is formatted as the following example: "{@code a, b --> c, d}"
	 */
	public Relation(String[] names, String[] exprs){
		this.attrs = Attribute.getSet(names);
		this.fds = FuncDep.getSet(exprs);
	}

	/**
	 * Decompose the current relation into a set of relations that satisfy 3NF, 
	 * by using the Lossless Join &amp; Dependency Preservation algorithm
	 * @return a set of decomposed relations
	 */
        public Set<Relation> decomposeTo2NF(){
            Set<Relation> result = new HashSet<>();
                Set<FuncDep> mb = Algos.minimalBasis(Algos.check2NF(this.attrs,this.fds));
                Set<FuncDep> a = Algos.combineRight(mb);
                
		for(FuncDep fd : a){
                        //System.out.println(fd.getLeft());
                        //System.out.println(fd.getRight());
                    	Set<Attribute> attrsNow = new HashSet<>(fd.getLeft());
                        //System.out.println(attrsNow);
			attrsNow.addAll(fd.getRight());
                            
                        //System.out.println(attrsNow);
			Set<FuncDep> proj = Algos.projection(attrsNow, mb);
                        //System.out.println(proj);
			result.add(new Relation(attrsNow, proj));
		}
                Set<Relation> toRemove = new HashSet<>();
		for(Relation ab : result){
			for(Relation b : result){
				if(ab != b && ab.attrs.containsAll(b.attrs)){
					toRemove.add(b);
				}
			}
                        //System.out.println(toRemove);
		}
		result.removeAll(toRemove);
                Set<Set<Attribute>> keys = Algos.keys(this.attrs, mb);
		boolean contains = false;
		for(Relation r : result){
			for(Set<Attribute> k : keys){
				if(r.attrs.containsAll(k)){
                                        System.out.println(r);
					contains = true;
					break;
				}
			}
			if(contains){
				break;
			}
		}
		if(!contains){
			Set<Attribute> key = null;
			for(Set<Attribute> k : keys){
				key = k;
				break;
			}
			Set<FuncDep> proj = Algos.projection(key, mb);
                        System.out.println(key);
			result.add(new Relation(key, proj));
		}
		return result;
            
        }
	public Set<Relation> decomposeTo3NF(){
		Set<Relation> result = new HashSet<>();
		Set<FuncDep> mb = Algos.minimalBasis(this.fds);
                Set<FuncDep> ab = Algos.combineRight(mb);
		for(FuncDep fd : ab){
                        //System.out.println(fd.getLeft());
                        //System.out.println(fd.getRight());
                    	Set<Attribute> attrsNow = new HashSet<>(fd.getLeft());
                        //System.out.println(attrsNow);
			attrsNow.addAll(fd.getRight());
                        //System.out.println(attrsNow);
			Set<FuncDep> proj = Algos.projection(attrsNow, mb);
                        //System.out.println(proj);
			result.add(new Relation(attrsNow, proj));
		}
		Set<Relation> toRemove = new HashSet<>();
		for(Relation a : result){
			for(Relation b : result){
				if(a != b && a.attrs.containsAll(b.attrs)){
					toRemove.add(b);
				}
			}
                        //System.out.println(toRemove);
		}
		result.removeAll(toRemove);
		Set<Set<Attribute>> keys = Algos.keys(this.attrs, mb);
		boolean contains = false;
		for(Relation r : result){
			for(Set<Attribute> k : keys){
				if(r.attrs.containsAll(k)){
                                        //System.out.println(r);
					contains = true;
					break;
				}
			}
			if(contains){
				break;
			}
		}
		if(!contains){
			Set<Attribute> key = null;
			for(Set<Attribute> k : keys){
				key = k;
				break;
			}
			Set<FuncDep> proj = Algos.projection(key, mb);
			result.add(new Relation(key, proj));
		}
		return result;
	}
	
	/**
	 * Decompose the current relation into a set of relations that satisfies BCNF, 
	 * regardless the possible loss of FD's
	 * @return a set of decomposed relations
	 */
	public Set<Relation> decomposeToBCNF(){
		Set<Relation> result = new HashSet<>();
		
		//check if it's already in BCNF
		Set<FuncDep> violating = this.getFdsViolatingBCNF();
		if(violating.isEmpty()){
			result.add(this);
			return result;
		}
		
		//if not, pick a violating FD to decompose
		FuncDep pick = null;
		for(FuncDep fd : violating){
			pick = fd;
			break;
		}
		Set<Attribute> lefts = pick.getLeft();
                
		Set<Attribute> attrs1 = Algos.closure(lefts, this.fds);
                
		Set<Attribute> attrs2 = new HashSet<>(this.attrs);
                
		attrs2.removeAll(attrs1);
		attrs2.addAll(lefts);
		Set<FuncDep> fds1 = Algos.projection(attrs1, this.fds);
		Set<FuncDep> fds2 = Algos.projection(attrs2, this.fds);
                
		
		//create two new relations
		Relation r1 = new Relation(attrs1, fds1);
		Relation r2 = new Relation(attrs2, fds2);
		
		//recursively decompose
		result.addAll(r1.decomposeToBCNF());
		result.addAll(r2.decomposeToBCNF());
		
		return result;

		
	}
	
	
	public Set<Attribute> getAttributes(){
		return new HashSet<>(this.attrs);
	}
	
	/**
	 * 
	 * @return all FD's that violate the 3NF; an empty set if it's already in 3NF
	 */
	public Set<FuncDep> getFdsViolating3NF(){
		return Algos.check3NF(this.attrs, this.fds);
	}
	
	/**
	 * 
	 * @return all FD's that violate the BCNF; an empty set if it's already in BCNF
	 */
	public Set<FuncDep> getFdsViolatingBCNF(){
		return Algos.checkBCNF(this.attrs, this.fds);
	}
	
	/**
	 * 
	 * @return a set of {@code FuncDep} objects that involved in this relation
	 */
	public Set<FuncDep> getFuncDeps(){
		return new HashSet<>(this.fds);
	}
	
	/**
	 * Compute all the candidate keys in this relation
	 * @return a set of candidate keys, and each itself is a set of attributes
	 */
	public Set<Set<Attribute>> getKeys(){
		return Algos.keys(this.attrs, this.fds);
	}
	
	/**
	 * Compute all the superkeys (including candidate keys) in this relation
	 * @return a set of superkeys, and each itself is a set of attributes
	 */
	public Set<Set<Attribute>> getSuperkeys(){
		return Algos.superKeys(this.attrs, this.fds);
	}
	
	@Override
	public int hashCode(){
		int hash = 17;
		for(Attribute a : this.attrs){
			hash = 31 * hash + a.hashCode();
		}
		for(FuncDep fd : this.fds){
			hash = 31 * hash + fd.hashCode();
		}
		return hash;
	}
	
	/**
	 * 
	 * @return {@code true} if this relation is already in the third normal form (3NF)
	 */
	public boolean is3NF(){
		return Algos.check3NF(this.attrs, this.fds).isEmpty();
	}
	
	/**
	 *  
	 * @return {@code true} if this relation is already in Boyce-Codd normal form (BCNF)
	 */
	public boolean isBCNF(){
		return Algos.checkBCNF(this.attrs, this.fds).isEmpty();
	}
	
	@Override
	public String toString(){
		StringBuilder sb = new StringBuilder(Attribute.AVERAGE_LENGTH * 50);
		sb.append("Attributes:\n");
		for(Attribute a : this.attrs){
			sb.append(a);
			sb.append(", ");
		}
		sb.delete(sb.length() - 2, sb.length() - 1);
		sb.append("\nFunctional Dependencies: \n");
		for(FuncDep fd : this.fds){
			sb.append(fd);
			sb.append('\n');
		}
		sb.deleteCharAt(sb.length() - 1);
		return sb.toString();
	}

}