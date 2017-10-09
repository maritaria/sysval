/*
 * Test data strategy for IgnitionTest.
 *
 * Generated by JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178), 2017-10-09 22:23 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */
import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * Test data strategy for IgnitionTest. Provides
 * class-scope test values for type java.lang.String[].
 * 
 * @author JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178)
 * @version 2017-10-09 22:23 +0200
 */
public /*@ nullable_by_default */ class IgnitionTest_ClassStrategy_java_lang_String1DArray 
  extends PackageStrategy_java_lang_String1DArray {
  /**
   * @return class-scope values for type java.lang.String[].
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Object>
    (new Object[] 
     { /* add class-scope java.lang.String[] values or generators here */ });
  }

  /**
   * The maximum length of generated arrays can be controlled here for
   * parameters of type java.lang.String[]
   * in this class by changing the parameter to <code>setMaxLength</code>.
   * In addition, the data generators used can be changed by adding 
   * additional data class lines, or by removing some of the automatically 
   * generated ones. Note that lower-level strategies can override any 
   * behavior specified here by calling the same control methods in 
   * their own constructors.
   *
   * @see NonPrimitiveStrategy#addDataClass(Class<?>)
   * @see NonPrimitiveStrategy#clearDataClasses()
   * @see ArrayStrategy#setMaxLength(int)
   */
  public IgnitionTest_ClassStrategy_java_lang_String1DArray() {
    super();
    // uncomment to control the maximum array length, 1 by default
    // setMaxLength(1); 
    setReflective(true);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
