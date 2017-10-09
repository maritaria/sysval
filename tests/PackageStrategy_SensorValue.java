/*
 * Test data strategy for package .
 *
 * Generated by JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178), 2017-10-09 22:23 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */
import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
import org.jmlspecs.jmlunitng.strategy.ObjectStrategy;

/**
 * Test data strategy for package <default>. Provides
 * package-scope test values for type SensorValue.
 * 
 * @author JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178)
 * @version 2017-10-09 22:23 +0200
 */
public /*@ nullable_by_default */ class PackageStrategy_SensorValue 
  extends ObjectStrategy {
  /**
   * @return package-scope values for type SensorValue.
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<Object>
    (new Object[] 
     { /* add package-scope SensorValue values or generators here */ });
  }

  /**
   * Constructor. 
   * The use of reflection can be controlled here for method 
   * parameters of type SensorValue
   * in this package by changing the parameters to <code>setReflective</code>
   * and <code>setMaxRecursionDepth<code>.
   * In addition, the data generators used can be changed by adding 
   * additional data class lines, or by removing some of the automatically 
   * generated ones. Note that lower-level strategies can override any 
   * behavior specified here by calling the same control methods in 
   * their own constructors.
   *
   * @see NonPrimitiveStrategy#addDataClass(Class<?>)
   * @see NonPrimitiveStrategy#clearDataClasses()
   * @see ObjectStrategy#setReflective(boolean)
   * @see ObjectStrategy#setMaxRecursionDepth(int)
   */
  public PackageStrategy_SensorValue() {
    super(SensorValue.class);
    setReflective(true);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
