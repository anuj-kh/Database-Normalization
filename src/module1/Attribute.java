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
public final class Attribute {
	
	protected static final int AVERAGE_LENGTH = 10;
	
	/**
	 * Get a set of attributes with one single method
	 * @param names a formatted {@code String} as in the following example: "username, password, favApp, lastLogin" (white spaces are optional)
	 * @return a set of attributes
	 */
	public static Set<Attribute> getSet(String names){
		if(names.equals("")){
			return new HashSet<>();
		}
		names = names.replaceAll("\\s+","");
		return getSet(names.split(","));
	}
	
	/**
	 * Get a set of attributes with one single method
	 * @param names a String array in which each element will be used to create an {@code Attribute}
	 * @return a set of attributes
	 */
	public static Set<Attribute> getSet(String[] names){
		Set<Attribute> attrs = new HashSet<>();
		for(String s : names){
			attrs.add(Attribute.of(s));
		}
		return attrs;
	}
	
	/**
	 * A way to create an {@code Attribute} object without calling the constructor
	 * @param name the name of the attribute as a unique identifier
	 * @return a new {@code Attribute} object
	 */
	public static Attribute of(String name){
		return new Attribute(name);
	}

    static String[] toArray(Set<Attribute> sa) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }
	
	private final String name;
	
	/**
	 * The default constructor
	 * @param name the name of the attribute, as a unique identifier
	 */
	public Attribute(String name){
		this.name = name;
	}
	
	/**
	 * An {@code object} will equal to another if and only if they have the same {@code name} (case sensitive)
	 */
	@Override
	public boolean equals(Object o){
		if(o == this){
			return true;
		}
		if(!(o instanceof Attribute)){
			return false;
		}
		Attribute a = (Attribute)o;
		return a.name.equals(this.name);
	}
	
	/**
	 * 
	 * @return the name of the attribute
	 */
	public String getName(){
		return this.name;
	}
	
	@Override
	public int hashCode(){
		return this.name.hashCode();
	}
	
	@Override
	public String toString(){
		return this.name;
	}

}