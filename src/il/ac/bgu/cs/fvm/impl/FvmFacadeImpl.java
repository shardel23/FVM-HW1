package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement createTransitionSystem
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
        TransitionSystem<Pair<S1, S2>, A, P> system = createTransitionSystem();
        ArrayList<Pair<S1, S2>> states = new ArrayList<>(ts1.getStates().size() * ts2.getStates().size());
        for(S1 ts1State : ts1.getStates()){
            for(S2 ts2State : ts2.getStates()){
                states.add(new Pair<>(ts1State, ts2State));
            }
        }
        system.addAllStates(states);

        Set<A> systemActions = new HashSet<>();
        systemActions.addAll(ts1.getActions());
        systemActions.addAll(ts2.getActions());
        system.addAllActions(systemActions);

        Set<P> systemProp = new HashSet<>();
        systemProp.addAll(ts1.getAtomicPropositions());
        systemProp.addAll(ts2.getAtomicPropositions());
        system.addAllAtomicPropositions(systemProp);

        for(Transition<S1, A> transition : ts1.getTransitions()){
            for(Pair<S1, S2> pair1 : getPairsOfLeft(system, transition.getFrom())) {
                for(Pair<S1, S2> pair2 : getPairsOfLeft(system, transition.getTo())){
                    if(pair1.second.equals(pair2.second)){
                        system.addTransition(new Transition<>(pair1, transition.getAction(), pair2));
                    }
                }
            }
        }

        for(Transition<S2, A> transition : ts2.getTransitions()){
            for(Pair<S1, S2> pair1 : getPairsOfRight(system, transition.getFrom())) {
                for(Pair<S1, S2> pair2 : getPairsOfRight(system, transition.getTo())){
                    if(pair1.first.equals(pair2.first)){
                        system.addTransition(new Transition<>(pair1, transition.getAction(), pair2));
                    }
                }
            }
        }

        //TODO: check if needed shallow or deep
        for(S1 state1 : ts1.getInitialStates()){
            for(S2 state2 : ts2.getInitialStates()){
                system.setInitial(new Pair<S1, S2>(state1, state2), true);
            }
        }

        for(Pair<S1, S2> state : system.getStates()){
            for(P label : ts1.getLabel(state.first)){
                system.addToLabel(state, label);
            }
            for(P label : ts2.getLabel(state.second)){
                system.addToLabel(state, label);
            }
        }

        return system;
    }

    private<S1, S2, A, P> Set<Pair<S1, S2>> getPairsOfLeft(TransitionSystem<Pair<S1, S2>, A, P> ts, S1 s){
        Set<Pair<S1, S2>> pairs = new HashSet<Pair<S1, S2>>();
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

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
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
