package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
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
        return new TransitionSystemImpl<>();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        Set<A> actions = ts.getActions();
        Set<S> states = ts.getStates();
        if (ts.getInitialStates().size() > 1)
            return false;
        for (A act : actions) {
            for (S state : states) {
                if (post(ts, state, act).size() > 1) {
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

        if (ts.getInitialStates().size() > 1) {
            return false;
        }

        for (S state : states) {
            Set<S> statePosts = post(ts, state);
            for (S statePost : statePosts) {
                for (S statePost2 : statePosts) {
                    if (statePost == statePost2) {
                        continue;
                    } else {
                        //check labels;
                        Set<P> firstAP = ts.getLabel(statePost);
                        Set<P> secondAP = ts.getLabel(statePost2);
                        if (firstAP.equals(secondAP))
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
        Set<Transition<S, A>> transitions = ts.getTransitions();
        while (!sa.tail().isEmpty()) {
            S from = sa.head();
            as = sa.tail();
            A action = as.head();
            sa = as.tail();
            S to = sa.head();
            if (!ts.getStates().contains(from)) {
                throw new StateNotFoundException(from);
            }
            if (!ts.getActions().contains(action)) {
                throw new ActionNotFoundException(action);
            }
            if (!ts.getStates().contains(to)) {
                throw new StateNotFoundException(to);
            }
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
        if (!ts.getStates().contains(s)) {
            throw new StateNotFoundException(s);
        }
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
        if (!ts.getStates().contains(s)) {
            throw new StateNotFoundException(s);
        }
        if (!ts.getActions().contains(a)) {
            throw new ActionNotFoundException(a);
        }
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
        if (!ts.getActions().contains(a)) {
            throw new ActionNotFoundException(a);
        }
        Set<S> reachableStates = new HashSet<>();
        for (S state : c) {
            Set<S> reachableFromState = post(ts, state, a);
            reachableStates.addAll(reachableFromState);
        }
        return reachableStates;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        if (!ts.getStates().contains(s)) {
            throw new StateNotFoundException(s);
        }
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
        if (!ts.getStates().contains(s)) {
            throw new StateNotFoundException(s);
        }
        if (!ts.getActions().contains(a)) {
            throw new ActionNotFoundException(a);
        }
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
        if (!ts.getActions().contains(a)) {
            throw new ActionNotFoundException(a);
        }
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
        reachableStates.addAll(ts.getInitialStates());
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
        return new ProgramGraphImpl<>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> newTS =
                this.createTransitionSystem();

        generateStatesFromCircuit(c, newTS);
        generateActionsFromCircuit(c, newTS);
        generateInitialStatesFromCircuit(c, newTS);
        generateTransitionsFromCircuit(c, newTS);
        generateAtomicPropositionsFromCircuit(c, newTS);
        generateLabelsFromCircuit(c, newTS);
        removeUnreachableFromCircuit(c, newTS);

        return newTS;
    }

    private void removeUnreachableFromCircuit(Circuit c, TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> newTS) {
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> reachableStates = reach(newTS);
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> allStates = newTS.getStates();
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> statesToRemove = new HashSet<>();
        Set<Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>>> transitions =
                newTS.getTransitions();
        Set<Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>>> transitionsToRemove =
                new HashSet<>();
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : allStates) {
            if (!reachableStates.contains(state)) {
                for (Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> transition : transitions) {
                   if (transition.getTo().equals(state) || transition.getFrom().equals(state)) {
                       transitionsToRemove.add(transition);
                   }
                }
                for (Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> transition : transitionsToRemove) {
                    newTS.removeTransition(transition);
                }
                newTS.getLabelingFunction().remove(state);
                statesToRemove.add(state);
            }
        }
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : statesToRemove) {
            newTS.removeState(state);
        }
    }

    private void generateLabelsFromCircuit(Circuit c, TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> newTS) {
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : newTS.getStates()) {
            Map<String, Boolean> newLabel = new HashMap<>();
            newLabel.putAll(state.getFirst());
            newLabel.putAll(state.getSecond());
            newLabel.putAll(c.computeOutputs(state.getFirst(), state.getSecond()));
            for (String name : newLabel.keySet()) {
                if (newLabel.get(name)) {
                    newTS.addToLabel(state, name);
                }
            }
        }
    }

    private void generateAtomicPropositionsFromCircuit(Circuit c, TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> newTS) {
        for (String registerName : c.getRegisterNames()) {
            newTS.addAtomicProposition(registerName);
        }
        for (String inputPortName : c.getInputPortNames()) {
            newTS.addAtomicProposition(inputPortName);
        }
        for (String outputPortName : c.getOutputPortNames()) {
            newTS.addAtomicProposition(outputPortName);
        }
    }

    private void generateTransitionsFromCircuit(Circuit c, TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> newTS) {
        ArrayList<Map<String, Boolean>> inputPortsPermutations = new ArrayList<>();
        generateBooleanPermutations(inputPortsPermutations, c.getInputPortNames());
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : newTS.getStates()) {
            for (Map<String, Boolean> permutation : inputPortsPermutations) {
                Pair<Map<String, Boolean>, Map<String, Boolean>> updatedState =
                        new Pair<>(permutation, c.updateRegisters(state.getFirst(), state.getSecond()));
                newTS.addTransition(new Transition<>(state, permutation, updatedState));
            }
        }
    }

    private void generateInitialStatesFromCircuit(Circuit c, TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> newTS) {
        ArrayList<Map<String, Boolean>> inputPortsPermutations = new ArrayList<>();
        Map<String, Boolean> registersFalse = new HashMap<>();
        generateBooleanPermutations(inputPortsPermutations, c.getInputPortNames());
        for (String registerName : c.getRegisterNames()) {
            registersFalse.put(registerName, false);
        }
        for (Map<String, Boolean> inputPortsMap : inputPortsPermutations) {
            newTS.setInitial(new Pair<>(inputPortsMap, registersFalse), true);
        }
    }

    private void generateActionsFromCircuit(Circuit c, TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> newTS) {
        ArrayList<Map<String, Boolean>> inputPortsPermutations = new ArrayList<>();
        generateBooleanPermutations(inputPortsPermutations, c.getInputPortNames());
        newTS.addAllActions(inputPortsPermutations);
    }

    private void generateStatesFromCircuit(Circuit c, TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> newTS) {
        ArrayList<Map<String, Boolean>> registersPermutations = new ArrayList<>();
        ArrayList<Map<String, Boolean>> inputPortsPermutations = new ArrayList<>();
        generateBooleanPermutations(registersPermutations, c.getRegisterNames());
        generateBooleanPermutations(inputPortsPermutations, c.getInputPortNames());
        for (Map<String, Boolean> registersMap : registersPermutations) {
            for (Map<String, Boolean> inputPortsMap : inputPortsPermutations) {
                newTS.addState(new Pair<>(inputPortsMap, registersMap));
            }
        }
    }

    private void generateBooleanPermutations
            (ArrayList<Map<String, Boolean>> permutations,
             Set<String> names) {
        String[] namesArray = names.toArray(new String[0]);
        for (int i=0; i<Math.pow(2, namesArray.length); i++) {
            Map<String, Boolean> registersMap = new HashMap<>();
            int num = i;
            int index = 0;
            for (int j=0; j<namesArray.length; j++) {
                if (num % 2 == 1) {
                    registersMap.put(namesArray[index], true);
                } else {
                    registersMap.put(namesArray[index], false);
                }
                index++;
                num /= 2;
            }
            permutations.add(registersMap);
        }
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(
            ProgramGraph<L, A> pg,
            Set<ActionDef> actionDefs,
            Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> newTS =
                this.createTransitionSystem();

        // STATES
        Map<L, Set<Map<String, Object>>> locationToEvalsMap =
                generateEvalsToAllLocations(pg, actionDefs, conditionDefs);
        for (L location : pg.getLocations()) {
            for (Map<String, Object> eval : locationToEvalsMap.get(location)) {
                Pair<L, Map<String, Object>> state = new Pair<>(location, eval);
                newTS.addState(state);
                if (pg.getInitialLocations().contains(location) && isInitialEvaluation(pg, eval)) {
                    newTS.setInitial(state, true);
                }
            }
        }

        // ACTIONS
        Set<A> tsActions = new HashSet<>();
        for (PGTransition<L, A> pgTransition : pg.getTransitions()) {
            tsActions.add(pgTransition.getAction());
        }
        newTS.addAllActions(tsActions);

        // ATOMIC PROPOSITIONS
        for (L location : pg.getLocations()) {
            newTS.addAtomicProposition(location.toString());
        }
        for (ConditionDef conditionDef : conditionDefs) {
            newTS.addAtomicProposition(conditionDef.toString());
        }

        // LABELING
        for (Pair<L, Map<String, Object>> state : newTS.getStates()) {
            newTS.addToLabel(state, state.getSecond().toString());
        }

        // TRANSITIONS
        for (PGTransition<L, A> pgTransition : pg.getTransitions()) {
            L locationFrom = pgTransition.getFrom();
            String cond = pgTransition.getCondition();
            A action = pgTransition.getAction();
            L locationTo = pgTransition.getTo();
            for (Pair<L, Map<String, Object>> stateFrom : newTS.getStates()) {
                if (stateFrom.getFirst().equals(locationFrom)) {
                    for (Pair<L, Map<String, Object>> stateTo : newTS.getStates()) {
                        if (stateTo.getFirst().equals(locationTo)) {
                            Map<String, Object> evalFrom = stateFrom.getSecond();
                            Map<String, Object> evalTo = stateTo.getSecond();
                            for (ActionDef actionDef : actionDefs) {
                                if (actionDef.isMatchingAction(action.toString())) {
                                    if (actionDef.effect(evalFrom, action.toString()).equals(evalTo)) {
                                        newTS.addTransition(new Transition<>(
                                                stateFrom,
                                                action,
                                                stateTo
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        return newTS;
    }

    private <A, L> boolean isInitialEvaluation(ProgramGraph<L,A> pg, Map<String, Object> eval) {
        // TODO: Implement
        return false;
    }

    private <L, A> Map<L, Set<Map<String, Object>>> generateEvalsToAllLocations(
            ProgramGraph<L, A> pg,
            Set<ActionDef> actionDefs,
            Set<ConditionDef> conditionDefs) {
        Map<L, Set<Map<String, Object>>> locationToEvalsMap = new HashMap<>();
        Map<String, Object> initialEval = getInitialEval(pg);
        Set<PGTransition<L, A>> pgTransitions = pg.getTransitions();
        Set<L> pgInitialLocations = pg.getInitialLocations();
        for (L initialLocation : pgInitialLocations) {
            generateEvalsToAllLocations(
                    locationToEvalsMap,
                    actionDefs,
                    conditionDefs,
                    pgTransitions,
                    initialLocation,
                    initialEval);
        }
        return locationToEvalsMap;
    }

    private <L, A> void generateEvalsToAllLocations(
            Map<L, Set<Map<String, Object>>> locationToEvalsMap,
            Set<ActionDef> actionDefs,
            Set<ConditionDef> conditionDefs,
            Set<PGTransition<L,A>> pgTransitions,
            L location,
            Map<String, Object> eval) {
        for (PGTransition<L, A> pgTransition : pgTransitions) {
            L from = pgTransition.getFrom();
            if (from.equals(location)) {
                String cond = pgTransition.getCondition();
                for (ConditionDef conditionDef : conditionDefs) {
                    if (conditionDef.evaluate(eval, cond)) {
                        A action = pgTransition.getAction();
                        for (ActionDef actionDef : actionDefs) {
                            if (actionDef.isMatchingAction(action.toString())) {
                                Map<String, Object> newEval =
                                        actionDef.effect(eval, action.toString());
                                L to = pgTransition.getTo();
                                if (locationToEvalsMap.get(to).add(newEval)) {
                                    generateEvalsToAllLocations(
                                            locationToEvalsMap,
                                            actionDefs,
                                            conditionDefs,
                                            pgTransitions,
                                            to,
                                            newEval);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    private <L, A> Map<String, Object> getInitialEval(ProgramGraph<L, A> pg) {
        pg.getInitalizations();
        return null;
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
