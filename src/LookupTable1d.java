/**
 * This class encapsulates one dimensional lookup table.
 */
class LookupTable1d {

	/** The only (one dimension, x) scale for this lookup table. */
	LookupScale scaleX;
	
	/** The lookup values of this table. Contrary to the scales 
	 *  there are no sortedness requirements of any kind.
	 */
	int[] lookupValues;
	
	// INVARIANT
	//@ invariant scaleX.values.length == lookupValues.length;
	
	/**
	 * Constructs the lookup table
	 * @param scale the associated (x) scale
	 * @param lookupValues the table values
	 */
	// CONTRACT
	//@ normal_behavior
	//@requires scale.values.length == lookupValues.length;
	//@ensures this.scaleX == scale;
	//@ensures this.lookupValues == lookupValues;
	LookupTable1d(LookupScale scale, int[] lookupValues) {
		this.scaleX = scale;
		this.lookupValues = lookupValues;
	}
	
	/**
	 * Looks up the sensor value in the this table.
	 * @param sv the sensor value to look up
	 * @return the (interpolated) value from the table
	 */
	/*@ pure @*/
	int getValue(SensorValue sv) {
		ScaleIndex si = scaleX.lookupValue(sv);
		int i = si.getIntPart();
		int f = si.getFracPart();
		int v = lookupValues[i];
		if(i<lookupValues.length-1 && f > 0) {
			int vn = lookupValues[i+1];
			//@ assert (v - vn) != 0;
			v = v + ((((vn - v) * 100) / f) / 100);//NOTE: Scaling not applied, just adding the percentage
		}
		// ASSERTION(S)
		// (note, what you want to check here would normally
		//  be part of the postcondition, but would produce a very
		//  elaborate specification).
		
		// the resulting value must be between any two adjacent elements in the lookupValues.
		
		//@ assert (\exists int j; j >= 0 && j < lookupValues.length - 1; v >= lookupValues[j] && v <= lookupValues[j+1]);
		
		return v;
	}
}
