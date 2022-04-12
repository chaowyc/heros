package heros.problems.incremental;

import heros.incremental.UpdatableWrapper;
import soot.NullType;
import soot.Type;
import soot.Value;
import soot.jimple.internal.JimpleLocal;
import soot.toolkits.scalar.Pair;

public class UpdatablePossibleType implements UpdatableWrapper<Pair<Value, Type>> {

    private UpdatableWrapper<Value> value = null;
    private UpdatableWrapper<Type> type = null;

    public static final UpdatablePossibleType zero = new UpdatablePossibleType();

    private static final Value EMPTY_VALUE = new JimpleLocal("<<zero>>", NullType.v());

    private UpdatablePossibleType() {
    }

    public UpdatablePossibleType(Pair<UpdatableWrapper<Value>, UpdatableWrapper<Type>> n) {
        this.value = n.getO1();
        this.type = n.getO2();
    }

    public UpdatablePossibleType(UpdatableWrapper<Value> value, UpdatableWrapper<Type> type) {
        this.value = value;
        this.type = type;
    }

    @Override
    public void notifyReferenceChanged(Object oldObject, Object newObject) {
        this.value.notifyReferenceChanged(oldObject, newObject);
        this.type.notifyReferenceChanged(oldObject, newObject);
    }

    @Override
    public Pair<Value, Type> getContents() {
        return new Pair<Value, Type>(getValue(), getType());
    }

    @Override
    public String toString() {
        return value + " -> " + type;
    }

    @Override
    public boolean equals(Object another) {
        if (super.equals(another))
            return true;

        if (another == null)
            return false;
        if (!(another instanceof UpdatablePossibleType))
            return false;
        UpdatablePossibleType urd = (UpdatablePossibleType) another;

        if (this.value == null)
        { if (urd.value != null) return false; }
        else { if (!this.value.equals(urd.value)) return false; }

        if (this.type == null)
        { if (urd.type != null) return false; }
        else { if (!this.type.equals(urd.type)) return false; }

        return true;
    }

    public Value getValue() {
        if (value == null)
            return EMPTY_VALUE;
        return this.value.getContents();
    }

    public Type getType() {
        return this.type.getContents();
    }

}