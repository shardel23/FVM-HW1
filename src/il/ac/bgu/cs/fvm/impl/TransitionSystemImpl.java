package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
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
        if (transitions.contains(t)) {
            throw new FVMException("Can't add transition " + t + ". " +
                    "this transition is already part of the transition system.");
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
        Set<P> currentLabels = labels.get(s);
        if (currentLabels == null) {
            throw new FVMException("Can't label state " + s + ". " +
                    "the state is not part of the transition system.");
        }
        if (currentLabels.contains(l)) {
            throw new FVMException("Can't label state " + s + " with " + l + ". " +
                    "this label is already part of the state's labels.");
        }
        currentLabels.add(l);
    }

    @Override
    public Set<P> getLabel(S s) {
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
        if (!actions.remove(a)) {
            throw new FVMException("Can't remove action " + a + ". " +
                    "this action is not part of the transition system.");
        }
        for (Transition<S, A> transition : transitions) {
            if (transition.getAction().equals(a)) {
                transitions.remove(transition);
            }
        }
    }

    @Override
    public void removeAtomicProposition(P p) throws FVMException {
        if (!atomicPropositions.remove(p)) {
            throw new FVMException("Can't remove atomic proposition " + p + ". " +
                    "this atomic proposition is not part of the transition system.");
        }
        for (Set<P> label : labels.values()) {
            label.remove(p);
        }
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
        if (!states.remove(s)) {
            throw new FVMException("Can't remove state " + s + ". " +
                    "this state is not part of the transition system.");
        }
        labels.remove(s);
        for (Transition<S, A> transition : transitions) {
            if (transition.getFrom().equals(s) || transition.getTo().equals(s)) {
                transitions.remove(transition);
            }
        }
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
