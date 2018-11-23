package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import java.io.InputStream;
import java.util.*;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
        return new TransitionSystem<>() {

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
        };
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        Set<A> actions = ts.getActions();
        Set<S> states = ts.getStates();
        if(ts.getInitialStates().size() > 1)
            return false;
        for(A act : actions){
            for(S state : states){
                if(post(ts, state, act).size() > 1){
                    return false;
                }
            }
        }
        return true;
    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        Set<S> states = ts.getStates();
        Set<P> APs = ts.getAtomicPropositions();

        for(S state : states){
            Set<S> statePosts = post(ts, state);
            for(S statePost : statePosts){
                for(S statePost2 : statePosts){
                    if(statePost == statePost2){
                        continue;
                    }
                    else{
                        //check labels;
                        Set<P> firstAP = ts.getLabel(statePost);
                        Set<P> secondAP = ts.getLabel(statePost2);
                        if(firstAP.equals(secondAP))
                            return false;
                    }
                }
            }
        }
        return true;
    }

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return (isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e));
    }

    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        AlternatingSequence<S, A> sa = e;
        AlternatingSequence<A, S> as;
        Set<Transition<S,A>> transitions = ts.getTransitions();
        while (!sa.tail().isEmpty()) {
            S from = sa.head();
            as = sa.tail();
            A action = as.head();
            sa = as.tail();
            S to = sa.head();
            if (!transitions.contains(new Transition<>(from, action, to))) {
                return false;
            }
        }
        return true;
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (!isExecutionFragment(ts, e)) {
            return false;
        }
        Set<S> i = ts.getInitialStates();
        return (i.contains(e.head()));
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (!isExecutionFragment(ts, e)) {
            return false;
        }
        return (post(ts, e.last()).isEmpty());
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        return (post(ts, s).isEmpty());
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> reachableStates = new HashSet<>();
        Set<? extends Transition<S, ?>> transitions = ts.getTransitions();
        for (Transition<S,?> transition : transitions) {
            if (transition.getFrom().equals(s)) {
                reachableStates.add(transition.getTo());
            }
        }
        return reachableStates;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> reachableStates = new HashSet<>();
        for (S state : c) {
            Set<S> reachableFromState = post(ts, state);
            reachableStates.addAll(reachableFromState);
        }
        return reachableStates;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S> reachableStates = new HashSet<>();
        Set<Transition<S,A>> transitions = ts.getTransitions();
        for (Transition<S,A> transition : transitions) {
            if (transition.getFrom().equals(s) && transition.getAction().equals(a)) {
                reachableStates.add(transition.getTo());
            }
        }
        return reachableStates;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> reachableStates = new HashSet<>();
        for (S state : c) {
            Set<S> reachableFromState = post(ts, state, a);
            reachableStates.addAll(reachableFromState);
        }
        return reachableStates;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> preOfs = new HashSet<>();
        Set<? extends Transition<S, ?>> transitions = ts.getTransitions();
        for(Transition<S,?> transition : transitions){
            if(transition.getTo().equals(s)){
                preOfs.add(transition.getFrom());
            }
        }
        return preOfs;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> pres = new HashSet<>();
        for(S state : c){
            pres.addAll(pre(ts,state));
        }
        return pres;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S> preOfsWitha = new HashSet<>();
        Set<Transition<S, A>> transitions = ts.getTransitions();
        for(Transition<S,A> transition : transitions){
            if(transition.getTo().equals(s) && transition.getAction().equals(a)){
                preOfsWitha.add(transition.getFrom());
            }
        }
        return preOfsWitha;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> pres = new HashSet<>();
        for(S state : c){
            pres.addAll(pre(ts,state, a));
        }
        return pres;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> reachableStates = new HashSet<>();
        for (S initialState : ts.getInitialStates()) {
            reach(initialState, ts, reachableStates);
        }
        return reachableStates;
    }

    private <S, A> void reach(S s, TransitionSystem<S, A, ?> ts, Set<S> reachableStates) {
        for (S state : post(ts, s)) {
            if (!reachableStates.contains(state)) {
                reachableStates.add(state);
                reach(state, ts, reachableStates);
            }
        }
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        TransitionSystem<Pair<S1, S2>, A, P> newTS = createTransitionSystem();

        createStates(ts1, ts2, newTS);
        createActions(ts1, ts2, newTS);
        createAtomicPropositions(ts1, ts2, newTS);
        createTransitions(ts1, ts2, newTS);
        createInitialStates(ts1, ts2, newTS);
        createLabels(ts1, ts2, newTS);

        return newTS;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem<Pair<S1, S2>, A, P> newTS = createTransitionSystem();

        createStates(ts1, ts2, newTS);
        createActions(ts1, ts2, newTS);
        createAtomicPropositions(ts1, ts2, newTS);
        createTransitions(ts1, ts2, newTS, handShakingActions);
        createInitialStates(ts1, ts2, newTS);
        createLabels(ts1, ts2, newTS);

        return newTS;
    }

    private<S1, S2, A, P> Set<Pair<S1, S2>> getPairsOfLeft(TransitionSystem<Pair<S1, S2>, A, P> ts, S1 s){
        Set<Pair<S1, S2>> pairs = new HashSet<>();
        for(Pair<S1, S2>  state : ts.getStates()){
            if(state.first.equals(s)){
                pairs.add(state);
            }
        }
        return pairs;
    }

    private<S1, S2, A> Set<Pair<S1, S2>> getPairsOfRight(TransitionSystem<Pair<S1, S2>, A, ?> ts, S2 s){
        Set<Pair<S1, S2>> pairs = new HashSet<>();
        for(Pair<S1, S2>  state : ts.getStates()){
            if(state.second.equals(s)){
                pairs.add(state);
            }
        }
        return pairs;
    }

    private <S1, S2, A, P> void createLabels(
            TransitionSystem<S1, A, P> ts1,
            TransitionSystem<S2, A, P> ts2,
            TransitionSystem<Pair<S1, S2>, A, P> newTS) {
        for (Pair<S1, S2> state : newTS.getStates()) {
            for (P label : ts1.getLabel(state.first)) {
                newTS.addToLabel(state, label);
            }
            for (P label : ts2.getLabel(state.second)) {
                newTS.addToLabel(state, label);
            }
        }
    }

    private <S1, S2, A, P> void createInitialStates(
            TransitionSystem<S1, A, P> ts1,
            TransitionSystem<S2, A, P> ts2,
            TransitionSystem<Pair<S1, S2>, A, P> newTS) {
        //TODO: check if needed shallow or deep
        for (S1 state1 : ts1.getInitialStates()) {
            for (S2 state2 : ts2.getInitialStates()) {
                newTS.setInitial(new Pair<>(state1, state2), true);
            }
        }
    }

    private <S1, S2, A, P> void createStates(
            TransitionSystem<S1, A, P> ts1,
            TransitionSystem<S2, A, P> ts2,
            TransitionSystem<Pair<S1, S2>, A, P> newTS) {
        ArrayList<Pair<S1, S2>> states =
                new ArrayList<>(ts1.getStates().size() * ts2.getStates().size());
        for (S1 ts1State : ts1.getStates()) {
            for (S2 ts2State : ts2.getStates()) {
                states.add(new Pair<>(ts1State, ts2State));
            }
        }
        newTS.addAllStates(states);
    }

    private <S1, S2, A, P> void createAtomicPropositions(
            TransitionSystem<S1, A, P> ts1,
            TransitionSystem<S2, A, P> ts2,
            TransitionSystem<Pair<S1, S2>, A, P> newTS) {
        Set<P> systemProp = new HashSet<>();
        systemProp.addAll(ts1.getAtomicPropositions());
        systemProp.addAll(ts2.getAtomicPropositions());
        newTS.addAllAtomicPropositions(systemProp);
    }

    private <S1, S2, A, P> void createActions(
            TransitionSystem<S1, A, P> ts1,
            TransitionSystem<S2, A, P> ts2,
            TransitionSystem<Pair<S1, S2>, A, P> newTS) {
        Set<A> systemActions = new HashSet<>();
        systemActions.addAll(ts1.getActions());
        systemActions.addAll(ts2.getActions());
        newTS.addAllActions(systemActions);
    }

    private <S1, S2, A, P> void createTransitions(
            TransitionSystem<S1, A, P> ts1,
            TransitionSystem<S2, A, P> ts2,
            TransitionSystem<Pair<S1, S2>, A, P> newTS) {
        for (Transition<S1, A> transition : ts1.getTransitions()) {
            for (Pair<S1, S2> pair1 : getPairsOfLeft(newTS, transition.getFrom())) {
                for (Pair<S1, S2> pair2 : getPairsOfLeft(newTS, transition.getTo())) {
                    if (pair1.second.equals(pair2.second)) {
                        newTS.addTransition(new Transition<>(pair1, transition.getAction(), pair2));
                    }
                }
            }
        }

        for (Transition<S2, A> transition : ts2.getTransitions()) {
            for (Pair<S1, S2> pair1 : getPairsOfRight(newTS, transition.getFrom())) {
                for (Pair<S1, S2> pair2 : getPairsOfRight(newTS, transition.getTo())) {
                    if (pair1.first.equals(pair2.first)) {
                        newTS.addTransition(new Transition<>(pair1, transition.getAction(), pair2));
                    }
                }
            }
        }
    }

    private <S1, S2, A, P> void createTransitions(
            TransitionSystem<S1, A, P> ts1,
            TransitionSystem<S2, A, P> ts2,
            TransitionSystem<Pair<S1, S2>, A, P> newTS,
            Set<A> handShakingActions) {
        for (A action : newTS.getActions()) {
            if (handShakingActions.contains(action)) {
                for (Transition<S1, A> transition1 : ts1.getTransitions()) {
                    for (Transition<S2, A> transition2 : ts2.getTransitions()) {
                        newTS.addTransition(
                                new Transition<>(
                                        new Pair<>(transition1.getFrom(), transition2.getFrom()),
                                        action,
                                        new Pair<>(transition1.getTo(), transition2.getTo())
                                )
                        );
                    }
                }
            }
            //TODO: check if needed shallow or deep
            else {
                for (Transition<S1, A> transition1 : ts1.getTransitions()) {
                    for (S2 s2 : ts2.getStates()) {
                        newTS.addTransition(
                                new Transition<>(
                                        new Pair<>(transition1.getFrom(), s2),
                                        action,
                                        new Pair<>(transition1.getTo(), s2)
                                )
                        );
                    }
                }
                for (Transition<S2, A> transition2 : ts2.getTransitions()) {
                    for (S1 s1 : ts1.getStates()) {
                        newTS.addTransition(
                                new Transition<>(
                                        new Pair<>(s1, transition2.getFrom()),
                                        action,
                                        new Pair<>(s1, transition2.getTo())
                                )
                        );
                    }
                }
            }
        }
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement createProgramGraph
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromCircuit
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement verifyAnOmegaRegularProperty
    }

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement LTL2NBA
    }

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement GNBA2NBA
    }

}
