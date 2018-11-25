package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class ProgramGraphImpl <L, A> implements ProgramGraph<L, A> {

    private String name;
    private Set<L> locations = new HashSet<>();
    private Set<L> initialLocations = new HashSet<>();
    private Set<PGTransition<L, A>> transitions = new HashSet<>();
    private Set<List<String>> initializations = new HashSet<>();

    @Override
    public void addInitalization(List<String> init) {
        initializations.add(init);
    }

    @Override
    public void setInitial(L location, boolean isInitial) {
        if (locations.contains(location)) {
            if (isInitial) {
                initialLocations.add(location);
            }
            else {
                initialLocations.remove(location);
            }
        }
        else {
            throw new IllegalArgumentException("Location " + location + " " +
                    "is not part of the PG.");
        }
    }

    @Override
    public void addLocation(L l) {
        locations.add(l);
    }

    @Override
    public void addTransition(PGTransition<L, A> t) {
        transitions.add(t);
    }

    @Override
    public Set<List<String>> getInitalizations() {
        return initializations;
    }

    @Override
    public Set<L> getInitialLocations() {
        return initialLocations;
    }

    @Override
    public Set<L> getLocations() {
        return locations;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public Set<PGTransition<L, A>> getTransitions() {
        return transitions;
    }

    @Override
    public void removeLocation(L l) {
        locations.remove(l);
        initialLocations.remove(l);
        for (PGTransition<L, A> transition : transitions) {
            if (transition.getFrom().equals(l) || transition.getTo().equals(l)) {
                transitions.remove(transition);
            }
        }
    }

    @Override
    public void removeTransition(PGTransition<L, A> t) {
        transitions.remove(t);
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }
}
