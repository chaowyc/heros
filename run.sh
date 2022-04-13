./gradlew fatJar
#java -Xmx35g -cp build/libs/heros.jar:lib/guava-23.0.jar:lib/junit-4.13.1.jar:lib/soot-4.3.0.jar heros.test.SingleJUnitTestRunner heros.test.IFDSReachingDefinitionsJUnit#newVersionJU_Propagate

java -Xmx35g -cp build/libs/heros.jar heros.test.SingleJUnitTestRunner heros.test.IFDSReachingDefinitionsJUnit#newVersionJU_Propagate