/*
 * Copyright 2003-2007 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.codehaus.groovy.reflection;

import groovy.lang.*;

import org.codehaus.groovy.reflection.stdclasses.*;
import org.codehaus.groovy.util.*;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.*;

/**
 * Handle for all information we want to keep about the class
 *
 * @author Alex.Tkachman
 */
public class ClassInfo extends ManagedConcurrentMap.Entry<Class,ClassInfo> {

    private final LazyCachedClassRef cachedClassRef;
    private final LazyClassLoaderRef artifactClassLoader;
    private final LockableObject lock = new LockableObject();
    public final int hash;

    private volatile int version;

    private MetaClass strongMetaClass;
    private ManagedReference<MetaClass> weakMetaClass;
    MetaMethod[] dgmMetaMethods = CachedClass.EMPTY;
    MetaMethod[] newMetaMethods = CachedClass.EMPTY;
    private ManagedConcurrentMap perInstanceMetaClassMap;

    private static ReferenceBundle softBundle = ReferenceBundle.getSoftBundle();
    private static ReferenceBundle weakBundle = ReferenceBundle.getWeakBundle();
    
    private static final ClassInfoSet globalClassSet = new ClassInfoSet(weakBundle);
    private static final ManagedLinkedList<ClassInfo> modifiedExpandos = new ManagedLinkedList<ClassInfo>(weakBundle);

    ClassInfo(ManagedConcurrentMap.Segment segment, Class klazz, int hash) {
        super (weakBundle, segment, klazz, hash);
        this.hash = hash;
        cachedClassRef = new LazyCachedClassRef(softBundle, this);
        artifactClassLoader = new LazyClassLoaderRef(softBundle, this);
    }

    public int getVersion() {
        return version;
    }

    public void incVersion() {
        version++;
    }

    public ExpandoMetaClass getModifiedExpando() {
        return strongMetaClass == null ? null : strongMetaClass instanceof ExpandoMetaClass ? (ExpandoMetaClass)strongMetaClass : null;
    }

    public static void clearModifiedExpandos() {
        for (Iterator<ClassInfo> it = modifiedExpandos.iterator(); it.hasNext(); ) {
            ClassInfo info = it.next();
            it.remove();
            info.setStrongMetaClass(null);
        }
    }

    public CachedClass getCachedClass() {
        return cachedClassRef.get();
    }

    public ClassLoaderForClassArtifacts getArtifactClassLoader() {
        return artifactClassLoader.get();
    }

    public static ClassInfo getClassInfo (Class cls) {
        return (ClassInfo) globalClassSet.getOrPut(cls,null);
    }
    
    public static void remove(Class<?> cls) {
    	globalClassSet.remove(cls);
    }

    public MetaClass getStrongMetaClass() {
        return strongMetaClass;
    }

    public void setStrongMetaClass(MetaClass answer) {
        version++;
        
        MetaClass strongRef = strongMetaClass;

        if (strongMetaClass instanceof ExpandoMetaClass) {
          ((ExpandoMetaClass)strongMetaClass).inRegistry = false;
          for (Iterator<ClassInfo> itr = modifiedExpandos.iterator(); itr.hasNext(); ) {
              ClassInfo info = itr.next();
              if(info == this) {
                  itr.remove();
              }
          }
        }

        strongMetaClass = answer;

        if (answer instanceof ExpandoMetaClass) {
          ((ExpandoMetaClass)strongMetaClass).inRegistry = true;
          modifiedExpandos.add(this);
        }

        replaceWeakMetaClassRef(null);
    }

    public MetaClass getWeakMetaClass() {
        return weakMetaClass == null ? null : weakMetaClass.get();
    }

    public void setWeakMetaClass(MetaClass answer) {
        version++;

        strongMetaClass = null;
        ManagedReference<MetaClass> newRef = null;
        if (answer != null) {
           weakMetaClass = new ManagedReference<MetaClass> (softBundle,answer);
        }
        replaceWeakMetaClassRef(newRef);
    }
    
    private void replaceWeakMetaClassRef(ManagedReference<MetaClass> newRef) {
        // safe value here to avoid multiple reads with possibly
        // differing values due to concurrency
        ManagedReference<MetaClass> weakRef = weakMetaClass;
        if (weakRef != null) {
            weakRef.clear();
        }
        weakMetaClass = newRef;
   }

    public MetaClass getMetaClassForClass() {
        return strongMetaClass != null ? strongMetaClass : weakMetaClass == null ? null : weakMetaClass.get();
    }

    private MetaClass getMetaClassUnderLock() {
        MetaClass answer = getStrongMetaClass();
        if (answer!=null) return answer;

        answer = getWeakMetaClass();
        final MetaClassRegistry metaClassRegistry = GroovySystem.getMetaClassRegistry();
        MetaClassRegistry.MetaClassCreationHandle mccHandle = metaClassRegistry.getMetaClassCreationHandler();

        if (answer != null) {
            boolean enableGloballyOn = (mccHandle instanceof ExpandoMetaClassCreationHandle);
            boolean cachedAnswerIsEMC = (answer instanceof ExpandoMetaClass);
            // if EMC.enableGlobally() is OFF, return whatever the cached answer is.
            // but if EMC.enableGlobally() is ON and the cached answer is not an EMC, come up with a fresh answer
            if(!enableGloballyOn || cachedAnswerIsEMC) {
                return answer;
            }
        }

        answer = mccHandle.create(get(), metaClassRegistry);
        answer.initialize();

        if (GroovySystem.isKeepJavaMetaClasses()) {
            setStrongMetaClass(answer);
        } else {
            setWeakMetaClass(answer);
        }
        return answer;
    }

    public final MetaClass getMetaClass() {
        MetaClass answer = getMetaClassForClass();
        if (answer != null) return answer;

        lock();
        try {
            return getMetaClassUnderLock();
        } finally {
            unlock();
        }
    }

    public MetaClass getMetaClass(Object obj) {
        final MetaClass instanceMetaClass = getPerInstanceMetaClass(obj);
        if (instanceMetaClass != null)
            return instanceMetaClass;

        lock();
        try {
            return getMetaClassUnderLock();
        } finally {
            unlock();
        }
    }

    public static int size () {
        return globalClassSet.size();
    }

    public static int fullSize () {
        return globalClassSet.fullSize();
    }

    @Override
    public void finalizeReference() {
        setStrongMetaClass(null);
        cachedClassRef.clear();
        artifactClassLoader.clear();

        super.finalizeReference();
    }

    private static CachedClass createCachedClass(Class klazz, ClassInfo classInfo) {
        if (klazz == Object.class)
            return new ObjectCachedClass(classInfo);

        if (klazz == String.class)
            return new StringCachedClass(classInfo);

        CachedClass cachedClass;
        if (Number.class.isAssignableFrom(klazz) || klazz.isPrimitive()) {
            if (klazz == Number.class) {
                cachedClass = new NumberCachedClass(klazz, classInfo);
            } else if (klazz == Integer.class || klazz ==  Integer.TYPE) {
                cachedClass = new IntegerCachedClass(klazz, classInfo, klazz==Integer.class);
            } else if (klazz == Double.class || klazz == Double.TYPE) {
                cachedClass = new DoubleCachedClass(klazz, classInfo, klazz==Double.class);
            } else if (klazz == BigDecimal.class) {
                cachedClass = new BigDecimalCachedClass(klazz, classInfo);
            } else if (klazz == Long.class || klazz == Long.TYPE) {
                cachedClass = new LongCachedClass(klazz, classInfo, klazz==Long.class);
            } else if (klazz == Float.class || klazz == Float.TYPE) {
                cachedClass = new FloatCachedClass(klazz, classInfo, klazz==Float.class);
            } else if (klazz == Short.class || klazz == Short.TYPE) {
                cachedClass = new ShortCachedClass(klazz, classInfo, klazz==Short.class);
            } else if (klazz == Boolean.TYPE) {
                cachedClass = new BooleanCachedClass(klazz, classInfo, false);
            } else if (klazz == Character.TYPE) {
                cachedClass = new CharacterCachedClass(klazz, classInfo, false);
            } else if (klazz == BigInteger.class) {
                cachedClass = new BigIntegerCachedClass(klazz, classInfo);
            } else if (klazz == Byte.class || klazz == Byte.TYPE) {
                cachedClass = new ByteCachedClass(klazz, classInfo, klazz==Byte.class);
            } else {
                cachedClass = new CachedClass(klazz, classInfo);
            }
        } else {
            if (klazz.getName().charAt(0) == '[')
              cachedClass = new ArrayCachedClass(klazz, classInfo);
            else if (klazz == Boolean.class) {
                cachedClass = new BooleanCachedClass(klazz, classInfo, true);
            } else if (klazz == Character.class) {
                cachedClass = new CharacterCachedClass(klazz, classInfo, true);
            } else if (Closure.class.isAssignableFrom(klazz)) {
                cachedClass = new CachedClosureClass (klazz, classInfo);
            } else {
                cachedClass = new CachedClass(klazz, classInfo);
            }
        }
        return cachedClass;
    }

    public void lock () {
        lock.lock();
    }

    public void unlock () {
        lock.unlock();
    }

    public MetaClass getPerInstanceMetaClass(Object obj) {
        if (perInstanceMetaClassMap == null)
          return null;

        return (MetaClass) perInstanceMetaClassMap.get(obj);
    }

    public void setPerInstanceMetaClass(Object obj, MetaClass metaClass) {
        version++;

        if (metaClass != null) {
            if (perInstanceMetaClassMap == null)
              perInstanceMetaClassMap = new ManagedConcurrentMap(ReferenceBundle.getWeakBundle());

            perInstanceMetaClassMap.put(obj, metaClass);
        }
        else {
            if (perInstanceMetaClassMap != null) {
              perInstanceMetaClassMap.remove(obj);
            }
        }
    }

    public boolean hasPerInstanceMetaClasses () {
        return perInstanceMetaClassMap != null;
    }

    public static class ClassInfoSet extends ManagedConcurrentMap<Class,ClassInfo> {
        public ClassInfoSet(ReferenceBundle bundle) {
            super(bundle);
        }

        protected Segment createSegment(Object segmentInfo,  int cap) {
            ReferenceBundle bundle = (ReferenceBundle) segmentInfo;
            if (bundle==null) throw new IllegalArgumentException("bundle must not be null ");

            return new Segment(bundle, cap);
        }

        static final class Segment extends ManagedConcurrentMap.Segment<Class,ClassInfo> {
            Segment(ReferenceBundle bundle, int initialCapacity) {
                super(bundle, initialCapacity);
            }

            protected ClassInfo createEntry(Class key, int hash, ClassInfo unused) {
                return new ClassInfo(this, key, hash);
            }
        }
    }

    private static class LazyCachedClassRef extends LazyReference<CachedClass> {
        private final ClassInfo info;

        LazyCachedClassRef(ReferenceBundle bundle, ClassInfo info) {
            super(bundle);
            this.info = info;
        }

        public CachedClass initValue() {
            return createCachedClass(info.get(), info);
        }
    }

    private static class LazyClassLoaderRef extends LazyReference<ClassLoaderForClassArtifacts> {
        private final ClassInfo info;

        LazyClassLoaderRef(ReferenceBundle bundle, ClassInfo info) {
            super(bundle);
            this.info = info;
        }

        public ClassLoaderForClassArtifacts initValue() {
            return new ClassLoaderForClassArtifacts(info.get());
        }
    }
}
