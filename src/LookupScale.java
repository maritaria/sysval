/** This class encapsulates lookup table scales. */

class LookupScale {
	
	/** Stores the scale (so called) break points.
	  * Scales are required to be strictly monotone,
	  * with raising values. */
	int[] values;

	// INVARIANT(S)
	//@ invariant (\forall int i; i >=0 && i < values.length - 2; values[i+1] - values[i] > 0 && values[i+2] - values[i+1] == values[i+1] - values[i]);
	//each pair must have a delta of larger than 0 and be equal to the delta of the next pair
	
	/**
	 * Construct the scale with predefined break points
	 * @param values the array with break point values
	 */
	// CONTRACT 
	//@ ensures (\forall int i; i >=0 && i < values.length; this.values[i]==values[i]);
	LookupScale(int[] values) {
		this.values = values;
	}
	
	/**
	 * Construct a linear scale that has size break points equally
	 * distributed between min and max values. 
	 * @param _min minimal value of the scale
	 * @param _max maximal value of the scale
	 * @param size number of break points in the scale
	 */
	// CONTRACT
	//@ normal_behavior
	//@ requires _max > _min;
	//@ requires size > 0;
	// requires ((_max - _min) % (size-1)) == 0;
	//@ ensures this.values[0]==_min;
	//@ ensures (\forall int i; i >=1 && i < this.values.length; this.values[i]== this.values[i-1] + (_max - _min)/(size-1));
	LookupScale(int _min, int _max, int size) {
		this.values = new int[size];
		//Mistake 2: doing size -1 doesnt allow the range of 2000-6000 to be divisible, off by one.
		int chunk = (_max - _min) / (size-1);
		this.values[0] = _min;
		//@ loop_invariant i >= 1 && i <= size && (\forall int j;j>=1 && j<i;this.values[j]-this.values[j-1] == chunk);
		for(int i=1; i<this.values.length; i++) {
		  this.values[i] = this.values[i-1] + chunk;
		  System.out.println(this.values[i]);
		};
		//@ assert this.values[this.values.length-1] == _max;
		//The invariant: is that the difference between min and max must be divisible by size
	}

	/**
	 * Looks up a sensor value in the scale and returns the scale index
	 * corresponding to the position of the sensor value in the scale. 
	 * @param sv the sensor value that should be looked up the scale
	 * @return the scale index (integral and fractional part)
	 */
	// CONTRACT
	//@ normal_behavior
	//@ requires sv.getValue() > this.values[this.values.length -1];
	//@ ensures \result.getIntPart() == this.values.length - 1;
	//@ ensures \result.getFracPart() == 0;
	//@ ensures \result.getSize() == this.values.length;
	//@
	//@ also
	//@
	//@ normal_behavior
	//@ requires sv.getValue() < this.values[0];
	//@ ensures \result.getIntPart() == 0;
	//@ ensures \result.getFracPart() == 0;
	//@ ensures \result.getSize() == this.values.length;
	//@
	//@ also
	//@
	//@ normal_behavior
	//@ requires sv.getValue() >= this.values[0];
	//@ requires sv.getValue() <= this.values[this.values.length - 1];
	//@ ensures this.values[\result.getIntPart()] <= sv.getValue();
	//@ ensures \result.getFracPart() >= 0;
	//@ ensures \result.getFracPart() < 100;
	//@ ensures \result.getSize() == this.values.length;
	ScaleIndex lookupValue(SensorValue sv) {
		int v = sv.getValue();
		// First get the integral part
		// The most convenient way to lookup scales is from the end
		int intPart = this.values.length - 1;
		while(intPart >= 0) {
			if(v >= this.values[intPart]) {
				break;
			}
			intPart--;
		}
		// ASSERTION
		//@ assert v >= this.values[intPart];
		//@ assert intPart >= 0;
		//@ assert intPart <= this.values.length - 1;
		int fracPart = 0;
		// Check border cases
		if(intPart == this.values.length - 1 || v < this.values[0]) {
			// ASSERTION(S)
			//@ assert v < this.values[0] || v >= this.values[this.values.length-1];
			return new ScaleIndex(intPart, fracPart, this.values.length);
		}
		// Then calculate the fractional part
		fracPart = (v - this.values[intPart]) * 100 / (this.values[intPart+1] - this.values[intPart]);
		// ASSERTION(S)
		//@ assert fracPart >= 0;
		//@ assert fracPart < 100;
		return new ScaleIndex(intPart, fracPart, this.values.length);
	}

	/**
	 * Provide a human readable version of this object, makes 
	 * the output of JMLUnitNG more readable.
	 */
	// skipesc;
	public String toString() {
		String r = "Scale of size "+this.values.length+": [";
		for(int i = 0; i<this.values.length; i++) {
			r += ""+(i==0 ? "" : ", ")+values[i];
		}
		r += "]";
		return r;
	}

}
