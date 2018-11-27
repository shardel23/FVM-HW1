package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class TransitionSystemImpl <S, A, P> implements TransitionSystem< S, A, P> {

    private String name;
    private Map<S, Boolean> states = new HashMap<>(); // Boolean is for isInitial
    private Map<S, Set<P>> labels = new HashMap<>();
    private Set<Transition<S, A>> transitions = new HashSet<>();
    private Set<A> actions = new HashSet<>();
    private Set<P> atomicPropositions = new HashSet<>();

    @Override
    public String getName() {
        return name;
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void addAction(A anAction) {
        actions.add(anAction);
    }

    @Override
    public void setInitial(S aState, boolean isInitial) throws StateNotFoundException {
        if (states.get(aState) == null) {
            throw new StateNotFoundException(aState);
        }
        states.put(aState, isInitial);
    }

    @Override
    public void addState(S s) {
        states.putIfAbsent(s, false);
        labels.putIfAbsent(s, new HashSet<>());
    }

    @Override
    public void addTransition(Transition<S, A> t) throws FVMException {
        if (!states.keySet().contains(t.getTo()) ||
                !states.keySet().contains(t.getFrom()) ||
                !actions.contains(t.getAction())) {
            throw new InvalidTransitionException(t);
        }
        transitions.add(t);
    }

    @Override
    public Set<A> getActions() {
        return actions;
    }

    @Override
    public void addAtomicProposition(P p) {
        atomicPropositions.add(p);
    }

    @Override
    public Set<P> getAtomicPropositions() {
        return atomicPropositions;
    }

    @Override
    public void addToLabel(S s, P l) throws FVMException {
        if (!atomicPropositions.contains(l)) {
            throw new InvalidLablingPairException(s, l);
        }
        labels.get(s).add(l);
    }

    @Override
    public Set<P> getLabel(S s) {
        if (labels.get(s) == null) {
            throw new StateNotFoundException(s);
        }
        return labels.get(s);
    }

    @Override
    public Set<S> getInitialStates() {
        Set<S> initialStates = new HashSet<>();
        for (S state : states.keySet()) {
            if (states.get(state)) {
                initialStates.add(state);
            }
        }
        return initialStates;
    }

    @Override
    public Map<S, Set<P>> getLabelingFunction() {
        return labels;
    }

    @Override
    public Set<S> getStates() {
        return states.keySet();
    }

    @Override
    public Set<Transition<S, A>> getTransitions() {
        return transitions;
    }

    @Override
    public void removeAction(A a) throws FVMException {
        for (Transition<S, A> transition : transitions) {
            if (transition.getAction().equals(a)) {
                throw new DeletionOfAttachedActionException(a, TransitionSystemPart.TRANSITIONS);
            }
        }
        actions.remove(a);
    }

    @Override
    public void removeAtomicProposition(P p) throws FVMException {
        for (Set<P> label : labels.values()) {
            if (label.contains(p)) {
                throw new DeletionOfAttachedAtomicPropositionException(
                        p, TransitionSystemPart.LABELING_FUNCTION);
            }
        }
        atomicPropositions.remove(p);
    }

    @Override
    public void removeLabel(S s, P l) {
        Set<P> currentLabels = labels.get(s);
        if (currentLabels != null) {
            currentLabels.remove(l);
        }
    }

    @Override
    public void removeState(S s) throws FVMException {
        for (Transition<S, A> transition : transitions) {
            if (transition.getFrom().equals(s) || transition.getTo().equals(s)) {
                throw new DeletionOfAttachedStateException(s, TransitionSystemPart.TRANSITIONS);
            }
        }
        if (labels.get(s) != null) {
            if (!labels.get(s).isEmpty()) {
                throw new DeletionOfAttachedStateException(s, TransitionSystemPart.LABELING_FUNCTION);
            }
        }
        if (states.get(s)) {
            throw new DeletionOfAttachedStateException(s, TransitionSystemPart.INITIAL_STATES);
        }
        states.remove(s);
    }

    @Override
    public void removeTransition(Transition<S, A> t) {
        transitions.remove(t);
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof TransitionSystem) {
            return false;
        }
        TransitionSystem ts2 = (TransitionSystem) other;
        return this.getStates().equals(ts2.getStates()) &&
                this.getInitialStates().equals(ts2.getInitialStates()) &&
                this.getLabelingFunction().equals(ts2.getLabelingFunction()) &&
                this.getTransitions().equals(ts2.getTransitions()) &&
                this.getActions().equals(ts2.getActions()) &&
                this.getAtomicPropositions().equals(ts2.getAtomicPropositions());
    }

    @Override
    public int hashCode() {
        //TODO: Implement
        return -1;
    }
}
