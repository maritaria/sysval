/**
 * An encapsulation class that stores the current value of a sensor readout.
 * The class is responsible for checking the sanity (staying within the 
 * allowable range) of the readouts and providing a fail-safe value in case
 * of failures.
 */
class SensorValue {

	int value;
	final int failSafe;
	final int minValue;
	final int maxValue;

	// INVARIANT(S)
	//@ invariant (value >= minValue && value <= maxValue) || (value == failSafe);
	//@ invariant failSafe < minValue || failSafe > maxValue;
	//@ invariant minValue < maxValue;
	//@ assignable value;

		/**
		 * @param failSafe
		 *            the default fail-safe value for this sensor
		 * @param minValue
		 *            minimum allowable value for this sensor
		 * @param maxValue
		 *            maximum allowable value for this sensor
		 */
		// CONTRACT
	//@ assignable value;
	//@ ensures this.failSafe == failSafe;
	//@ ensures this.minValue == minValue;
	//@ ensures this.maxValue == maxValue;
	//@ ensures this.value == failSafe;
	SensorValue(int failSafe, int minValue, int maxValue) {
		this.failSafe = failSafe;
		this.minValue = minValue;
		this.maxValue = maxValue;
		this.value = failSafe;
	}
	
	/**
	 * The newly read value is either within the allowable range
	 * or has to be substituted with a fail-safe. 
	 * @param newValue newly read value
	 */
	// CONTRACT
	//@ assignable value;
	//@ ensures (newValue < minValue || newValue > maxValue) ==> value==failSafe;
	//@ ensures (newValue >= minValue && newValue <= maxValue) ==> value==newValue;
	void readSensor(int newValue) {
		if(newValue < this.minValue || newValue > this.maxValue) {
			this.value = this.failSafe;
		}else{
			this.value = newValue;
		}
	}
	
	/**
	 * @return the most recently read value
	 */
	// CONTRACT
	//@ensures \result==value;
	int /* @pure */ getValue() {
		return this.value;
	}
	
	/**
	 * Provide a human readable version of this object, makes 
	 * the output of JMLUnitNG more readable.
	 */
	//skipesc;
	public String toString() {
		return "SensorValue <"+minValue+"-"+maxValue+", FS="+failSafe+"> = ["+value+"]";
	}
	
}
