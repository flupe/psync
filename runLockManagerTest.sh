#!/bin/bash
export JAVA_OPTS="-Xmx1536M -Xms256M -Xss64M"
scala_version1=2.11
scala_version2=2.11.1
BASEDIR=`dirname $0`
ivy_cache="$HOME/.ivy2/cache"

dep0="$BASEDIR/target/scala-${scala_version1}/*"
dep1="$ivy_cache/org.scala-lang/scala-library/jars/scala-library-${scala_version2}.jar"
dep2="$ivy_cache/org.scala-lang.modules/scala-xml_${scala_version1}/bundles/*"
dep3="$ivy_cache/org.apache.commons/commons-lang3/jars/*"
dep4="$ivy_cache/io.netty/netty-all/jars/*"
dep5="$ivy_cache/org.scala-lang/scala-pickling_${scala_version1}/jars/*"
dep6="$ivy_cache/org.scala-lang/scala-reflect/jars/scala-reflect-${scala_version2}.jar"

cp="$dep0:$dep1:$dep2:$dep3:$dep4:$dep5:$dep6"

#exec java -cp ${cp} -Dio.netty.leakDetectionLevel=advanced example.Main $*
exec java -cp ${cp} example.Main $*
