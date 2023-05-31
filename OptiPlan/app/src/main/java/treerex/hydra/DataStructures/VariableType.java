package treerex.hydra.DataStructures;

public enum VariableType {
    NOOP, // Which is a kind of an action but it is better to have a special type for it
    PRIMITIVE,
    ACTION,
    METHOD,
    PREDICATE
}