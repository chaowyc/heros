package heros.incremental;

import java.lang.ref.WeakReference;

/**
 * Wrapper class for decoupling arbitrary objects and making their references
 * exchangeable. This object holds a weak reference to the object being
 * wrapped, allowing for garbage collection.
 *
 * @param <N> The type of object to wrap.
 */
public class WeakUpdatableWrapper<N> implements UpdatableWrapper<N> {
	
	private WeakReference<N> contents;
	private int updateCount = 0;
	
	/**
	 * Creates a new instance of the UpdatableWrapper class.
	 * @param n The object to be wrapped
	 */
	public WeakUpdatableWrapper(N n) {
		this.contents = new WeakReference<N>(n);
	}
	
	@Override
	public N getContents() {
		return this.contents.get();
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public void notifyReferenceChanged(Object oldObject, Object newObject) {		
		if (oldObject != newObject && contents.get() == oldObject) {
			contents = new WeakReference<N>((N) newObject);
			updateCount++;
		}
	}

	@Override
	public String toString() {
		return contents.get() == null ? "<null>" : contents.get().toString();
	}

}
