package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.InterleavingActDef;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;
import org.antlr.v4.runtime.tree.ParseTree;

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
        for (Transition<S, ?> transition : transitions) {
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
        Set<Transition<S, A>> transitions = ts.getTransitions();
        for (Transition<S, A> transition : transitions) {
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
        for (Transition<S, ?> transition : transitions) {
            if (transition.getTo().equals(s)) {
                preOfs.add(transition.getFrom());
            }
        }
        return preOfs;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> pres = new HashSet<>();
        for (S state : c) {
            pres.addAll(pre(ts, state));
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
        for (Transition<S, A> transition : transitions) {
            if (transition.getTo().equals(s) && transition.getAction().equals(a)) {
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
        for (S state : c) {
            pres.addAll(pre(ts, state, a));
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
        removeUnreachableFromTS(newTS);

        return newTS;
    }

    private <P, S2, S1, A> void removeUnreachableFromTS(TransitionSystem<Pair<S1, S2>, A, P> ts) {
        Set<Pair<S1, S2>> reachable = reach(ts);
        Set<Pair<S1, S2>> allStates = ts.getStates();
        Set<Pair<S1, S2>> statesToRemove = new HashSet<>();
        Set<Transition<Pair<S1, S2>, A>> transitions = ts.getTransitions();
        Set<Transition<Pair<S1, S2>, A>> transitionsToRemove = new HashSet<>();
        for (Pair<S1, S2> state : allStates) {
            if (!reachable.contains(state)) {
                for (Transition<Pair<S1, S2>, A> transition : transitions) {
                    if (transition.getTo().equals(state) || transition.getFrom().equals(state)) {
                        transitionsToRemove.add(transition);
                    }
                }
                for (Transition<Pair<S1, S2>, A> transition : transitionsToRemove) {
                    ts.removeTransition(transition);
                }
                ts.getLabelingFunction().remove(state);
                statesToRemove.add(state);
            }
        }
        for (Pair<S1, S2> state : statesToRemove) {
            ts.removeState(state);
        }
    }

    private <S1, S2, A, P> Set<Pair<S1, S2>> getPairsOfLeft(TransitionSystem<Pair<S1, S2>, A, P> ts, S1 s) {
        Set<Pair<S1, S2>> pairs = new HashSet<>();
        for (Pair<S1, S2> state : ts.getStates()) {
            if (state.first.equals(s)) {
                pairs.add(state);
            }
        }
        return pairs;
    }

    private <S1, S2, A> Set<Pair<S1, S2>> getPairsOfRight(TransitionSystem<Pair<S1, S2>, A, ?> ts, S2 s) {
        Set<Pair<S1, S2>> pairs = new HashSet<>();
        for (Pair<S1, S2> state : ts.getStates()) {
            if (state.second.equals(s)) {
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
        for (Transition<S1, A> transition1 : ts1.getTransitions()) {
            A action1 = transition1.getAction();
            for (Transition<S2, A> transition2 : ts2.getTransitions()) {
                A action2 = transition2.getAction();
                if (action1.equals(action2) && handShakingActions.contains(action1)) {
                    newTS.addTransition(
                            new Transition<>(
                                    new Pair<>(transition1.getFrom(), transition2.getFrom()),
                                    action1,
                                    new Pair<>(transition1.getTo(), transition2.getTo())
                            )
                    );
                }
            }
        }
        for (Transition<S1, A> transition1 : ts1.getTransitions()) {
            A action = transition1.getAction();
            if (!handShakingActions.contains(action)) {
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
        }
        for (Transition<S2, A> transition2 : ts2.getTransitions()) {
            A action = transition2.getAction();
            if (!handShakingActions.contains(action)) {
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

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraphImpl<>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> newPG = createProgramGraph();

        // LOCATIONS
        for (L1 l1 : pg1.getLocations()) {
            for (L2 l2 : pg2.getLocations()) {
                Pair<L1, L2> location = new Pair<>(l1, l2);
                newPG.addLocation(location);
                if (pg1.getInitialLocations().contains(l1) && pg2.getInitialLocations().contains(l2)) {
                    newPG.setInitial(location, true);
                }
            }
        }

        // INITIALIZATION LIST
        for (List<String> initializations1 : pg1.getInitalizations()) {
            for (List<String> initializations2 : pg2.getInitalizations()) {
                ArrayList<String> combinedList = new ArrayList<>(initializations1);
                combinedList.addAll(initializations2);
                newPG.addInitalization(combinedList);
            }
        }
        if (pg1.getInitalizations().isEmpty()) {
            for (List<String> initializations2 : pg2.getInitalizations()) {
                newPG.addInitalization(initializations2);
            }
        }
        if (pg2.getInitalizations().isEmpty()) {
            for (List<String> initializations1 : pg1.getInitalizations()) {
                newPG.addInitalization(initializations1);
            }
        }

        // TRANSITIONS
        InterleavingActDef interleavingActDef = new ParserBasedInterleavingActDef();
        for (PGTransition<L1, A> transition1 : pg1.getTransitions()) {
            L1 from = transition1.getFrom();
            String cond = transition1.getCondition();
            A action = transition1.getAction();
            if (interleavingActDef.isOneSidedAction(action.toString())) {
                for (PGTransition<L2, A> transition2 : pg2.getTransitions()) {
                    String action1 = action.toString();
                    String action2 = transition2.getAction().toString();
                    String actions = action1 + "|" + action2;
                    if (interleavingActDef.isMatchingAction(actions) &&
                            action1.substring(0, action1.length() - 1).equals(action2.substring(0, action2.length() - 1))) {
                        newPG.addTransition(
                                new PGTransition<>(
                                        new Pair<>(transition1.getFrom(), transition2.getFrom()),
                                        cond,
                                        (A)actions,
                                        new Pair<>(transition1.getTo(), transition2.getTo())));
                    }
                }
            }
            else {
                L1 to = transition1.getTo();
                for (L2 loc2 : pg2.getLocations()) {
                    newPG.addTransition(
                            new PGTransition<>(
                                    new Pair<>(from, loc2),
                                    cond,
                                    action,
                                    new Pair<>(to, loc2)));
                }
            }
        }
        for (PGTransition<L2, A> transition2 : pg2.getTransitions()) {
            L2 from = transition2.getFrom();
            String cond = transition2.getCondition();
            A action = transition2.getAction();
            L2 to = transition2.getTo();
            if (!interleavingActDef.isOneSidedAction(action.toString())) {
                for (L1 loc1 : pg1.getLocations()) {
                    newPG.addTransition(
                            new PGTransition<>(
                                    new Pair<>(loc1, from),
                                    cond,
                                    action,
                                    new Pair<>(loc1, to)));
                }
            }
        }

        return newPG;
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

    private void generateBooleanPermutations(
            ArrayList<Map<String, Boolean>> permutations,
            Set<String> names) {
        String[] namesArray = names.toArray(new String[0]);
        for (int i = 0; i < Math.pow(2, namesArray.length); i++) {
            Map<String, Boolean> registersMap = new HashMap<>();
            int num = i;
            int index = 0;
            for (int j = 0; j < namesArray.length; j++) {
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

        List<Map<String, Object>> initialEvals = getInitialEvals(pg, actionDefs);
        Map<L, Set<Map<String, Object>>> locationToEvalsMap = new HashMap<>();
        for (Map<String, Object> initialEval : initialEvals) {
            Map<L, Set<Map<String, Object>>> evals = statesFromProgramGraph(pg, actionDefs, conditionDefs, newTS, initialEval);
            for (L location : evals.keySet()) {
                locationToEvalsMap.putIfAbsent(location, new HashSet<>());
                locationToEvalsMap.get(location).addAll(evals.get(location));
            }
        }
        actionsFromProgramGraph(pg, newTS);
        atomicPropositionsFromProgramGraph(pg, newTS, locationToEvalsMap);
        labelsFromProgramGraph(newTS);
        transitionsFromProgramGraph(pg, actionDefs, conditionDefs, newTS);

        return newTS;
    }

    private <L, A> void transitionsFromProgramGraph(
            ProgramGraph<L, A> pg, Set<ActionDef> actionDefs,
            Set<ConditionDef> conditionDefs,
            TransitionSystem<Pair<L, Map<String, Object>>, A, String> newTS) {
        InterleavingActDef interleavingActDef = new ParserBasedInterleavingActDef();
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
                            if (ConditionDef.evaluate(conditionDefs, evalFrom, cond)) {
                                if (interleavingActDef.isMatchingAction(action)) {
                                    if (ActionDef.effect(actionDefs, evalFrom, action.toString()).equals(evalTo)) {
                                        newTS.addTransition(new Transition<>(
                                                stateFrom,
                                                action,
                                                stateTo
                                        ));
                                    } else {
                                        if (evalFrom.equals(evalTo)) {
                                            newTS.addTransition(new Transition<>(
                                                    stateFrom,
                                                    action,
                                                    stateTo
                                            ));
                                        }
                                    }
                                } else {
                                    if (ActionDef.isMatchingAction(actionDefs, action.toString())) {
                                        if (ActionDef.effect(actionDefs, evalFrom, action.toString()).equals(evalTo)) {
                                            newTS.addTransition(new Transition<>(
                                                    stateFrom,
                                                    action,
                                                    stateTo
                                            ));
                                        }
                                    } else {
                                        if (evalFrom.equals(evalTo)) {
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
        }
    }

    private <L, A> void labelsFromProgramGraph(TransitionSystem<Pair<L, Map<String, Object>>, A, String> newTS) {
        for (Pair<L, Map<String, Object>> state : newTS.getStates()) {
            Map<String, Object> eval = state.second;
            for (String key : eval.keySet()) {
                newTS.addToLabel(state, key + " = " + eval.get(key));
            }
            if (state.getFirst() instanceof List) {
                for (Object o : (List)state.getFirst()) {
                    newTS.addToLabel(state, o.toString());
                }
            }
            else {
                newTS.addToLabel(state, state.getFirst().toString());
            }
        }
    }

    private <L, A> void atomicPropositionsFromProgramGraph(
            ProgramGraph<L, A> pg,
            TransitionSystem<Pair<L, Map<String, Object>>, A, String> newTS,
            Map<L, Set<Map<String, Object>>> locationToEvalsMap) {
        Set<String> atomicPropositions = new HashSet<>();
        for (L location : pg.getLocations()) {
            if (locationToEvalsMap.get(location) != null) {
                if (location instanceof List) {
                    atomicPropositions.addAll((List)location);
                }
                else {
                    newTS.addAtomicProposition(location.toString());
                }
            }
        }
        for (Set<Map<String, Object>> evaluation : locationToEvalsMap.values()) {
            for (Map<String, Object> map : evaluation) {
                for (String key : map.keySet())
                atomicPropositions.add(key + " = " + map.get(key));
            }
        }
        for (String ap : atomicPropositions) {
            newTS.addAtomicProposition(ap);
        }
    }

    private <L, A> void actionsFromProgramGraph(
            ProgramGraph<L, A> pg,
            TransitionSystem<Pair<L, Map<String, Object>>, A, String> newTS) {
        Set<A> tsActions = new HashSet<>();
        for (PGTransition<L, A> pgTransition : pg.getTransitions()) {
            tsActions.add(pgTransition.getAction());
        }
        newTS.addAllActions(tsActions);
    }

    private <L, A> Map<L, Set<Map<String, Object>>> statesFromProgramGraph(
            ProgramGraph<L, A> pg,
            Set<ActionDef> actionDefs,
            Set<ConditionDef> conditionDefs,
            TransitionSystem<Pair<L, Map<String, Object>>, A, String> newTS,
            Map<String, Object> initialEval) {
        Map<L, Set<Map<String, Object>>> locationToEvalsMap =
                generateEvalsToAllLocations(pg, actionDefs, conditionDefs, initialEval);
        for (L location : pg.getLocations()) {
            if (locationToEvalsMap.get(location) != null) {
                for (Map<String, Object> eval : locationToEvalsMap.get(location)) {
                    Pair<L, Map<String, Object>> state = new Pair<>(location, eval);
                    newTS.addState(state);
                    if (pg.getInitialLocations().contains(location) && eval.equals(initialEval)) {
                        newTS.setInitial(state, true);
                    }
                }
            }
        }
        return locationToEvalsMap;
    }

    private <L, A> Map<L, Set<Map<String, Object>>> generateEvalsToAllLocations(
            ProgramGraph<L, A> pg,
            Set<ActionDef> actionDefs,
            Set<ConditionDef> conditionDefs,
            Map<String, Object> initialEval) {
        Map<L, Set<Map<String, Object>>> locationToEvalsMap = new HashMap<>();
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
            Set<PGTransition<L, A>> pgTransitions,
            L location,
            Map<String, Object> eval) {
        InterleavingActDef interleavingActDef = new ParserBasedInterleavingActDef();
        locationToEvalsMap.computeIfAbsent(location, k -> new HashSet<>());
        locationToEvalsMap.get(location).add(eval);
        for (PGTransition<L, A> pgTransition : pgTransitions) {
            L from = pgTransition.getFrom();
            if (from.equals(location)) {
                String cond = pgTransition.getCondition();
                if (ConditionDef.evaluate(conditionDefs, eval, cond)) {
                    A action = pgTransition.getAction();
                    Map<String, Object> newEval = eval;
                    if (interleavingActDef.isMatchingAction(action)) {
                        newEval = interleavingActDef.effect(eval, action);
                    }
                    else if (ActionDef.isMatchingAction(actionDefs, action)) {
                        newEval = ActionDef.effect(actionDefs, eval, action);
                    }
                    if (newEval != null) {
                        L to = pgTransition.getTo();
                        locationToEvalsMap.computeIfAbsent(to, k -> new HashSet<>());
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
                    else {
                        newEval = eval;
                    }
                }
            }
        }
    }

    private <L, A> List<Map<String, Object>> getInitialEvals(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs) {
        List<Map<String, Object>> initialEvals = new ArrayList<>();
        Set<List<String>> initializationsSet = pg.getInitalizations();
        if (initializationsSet.isEmpty()) {
            initialEvals.add(new HashMap<>());
        }
        for (List<String> initializationList : initializationsSet) {
            Map<String, Object> result = new HashMap<>();
            for (String initialization : initializationList) {
                if (ActionDef.isMatchingAction(actionDefs, initialization)) {
                    result = ActionDef.effect(actionDefs, result, initialization);
                }
            }
            initialEvals.add(result);
        }
        return initialEvals;
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        List<ProgramGraph<L,A>> pgs = cs.getProgramGraphs();
        ProgramGraph<List<L>,A> resultPG = transposePG(pgs.get(0));
        for (int i=1; i<pgs.size(); i++) {
            ProgramGraph<Pair<List<L>, L>, A> product = interleave(resultPG, pgs.get(i));
            resultPG = transpose(product);
        }

        Set<ActionDef> actionDefs = new HashSet<>();
        Set<ConditionDef> conditionDefs = new HashSet<>();

        actionDefs.add(new ParserBasedActDef());
        //actionDefs.add(new ParserBasedInterleavingActDef());

        conditionDefs.add(new ParserBasedCondDef());

        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> resultTS = transitionSystemFromProgramGraph(resultPG, actionDefs, conditionDefs);
        return resultTS;
    }

    private <L, A> ProgramGraph<List<L>, A> transposePG(ProgramGraph<L, A> pg) {
        ProgramGraph<List<L>, A> newPG = createProgramGraph();

        for (L loc : pg.getLocations()) {
            List<L> newLoc = new ArrayList<>();
            newLoc.add(loc);
            newPG.addLocation(newLoc);
            if (pg.getInitialLocations().contains(loc)) {
                newPG.setInitial(newLoc, true);
            }
        }

        for (PGTransition<L,A> transition : pg.getTransitions()) {
            List<L> newFrom = new ArrayList<>();
            newFrom.add(transition.getFrom());
            List<L> newTo = new ArrayList<>();
            newTo.add(transition.getTo());
            newPG.addTransition(
                    new PGTransition<>(
                            newFrom,
                            transition.getCondition(),
                            transition.getAction(),
                            newTo));
        }

        for (List<String> initialization : pg.getInitalizations()) {
            newPG.addInitalization(initialization);
        }

        return newPG;
    }

    private <L, A> ProgramGraph<List<L>, A> transpose(ProgramGraph<Pair<List<L>, L>, A> pg) {
        ProgramGraph<List<L>, A> newPG = createProgramGraph();

        for (Pair<List<L>,L> loc : pg.getLocations()) {
            List<L> newLoc = new ArrayList<>();
            newLoc.addAll(loc.first);
            newLoc.add(loc.second);
            newPG.addLocation(newLoc);
            if (pg.getInitialLocations().contains(loc)) {
                newPG.setInitial(newLoc, true);
            }
        }

        for (PGTransition<Pair<List<L>,L>,A> transition : pg.getTransitions()) {
            List<L> newFrom = new ArrayList<>();
            newFrom.addAll(transition.getFrom().first);
            newFrom.add(transition.getFrom().second);
            List<L> newTo = new ArrayList<>();
            newTo.addAll(transition.getTo().first);
            newTo.add(transition.getTo().second);
            newPG.addTransition(
                    new PGTransition<>(
                            newFrom,
                            transition.getCondition(),
                            transition.getAction(),
                            newTo));
        }

        for (List<String> initialization : pg.getInitalizations()) {
            newPG.addInitalization(initialization);
        }

        return newPG;
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        ProgramGraph<String, String> ansPG = new ProgramGraphImpl<>();
        NanoPromelaParser.StmtContext root = NanoPromelaFileReader.pareseNanoPromelaFile(filename);
        String rootTXT = root.getText();

        ansPG.addLocation("");
        ansPG.addLocation(rootTXT);
        ansPG.setInitial(rootTXT, true);
        PGFromNP(ansPG, root, rootTXT, "", "", "");

        return ansPG;
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        ProgramGraph<String, String> ansPG = new ProgramGraphImpl<>();
        NanoPromelaParser.StmtContext root = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
        String rootTXT = root.getText();

        ansPG.addLocation("");
        ansPG.addLocation(rootTXT);
        ansPG.setInitial(rootTXT, true);
        PGFromNP(ansPG, root, rootTXT, "", "", "");

        return ansPG;
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        ProgramGraph<String, String> ansPG = new ProgramGraphImpl<>();
        NanoPromelaParser.StmtContext root = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
        String rootTXT = root.getText();

        ansPG.addLocation("");
        ansPG.addLocation(rootTXT);
        ansPG.setInitial(rootTXT, true);
        PGFromNP(ansPG, root, rootTXT, "", "", "");

        return ansPG;
    }

    private void PGFromNP(ProgramGraph<String, String> ansPG, ParseTree myRoot, String fromNode, String toNode, String cond, String post_np){
        int childCount = myRoot.getChildCount();
        String child;

        if(myRoot instanceof NanoPromelaParser.IfstmtContext)
            processIf(ansPG, myRoot, fromNode, toNode, cond, post_np);
        else if(myRoot instanceof NanoPromelaParser.DostmtContext)
            processDo(ansPG, myRoot, fromNode, toNode, cond, post_np);
        else if(!(myRoot instanceof NanoPromelaParser.StmtContext))
            processOtherCase(ansPG, myRoot, fromNode, toNode, cond, post_np);
        else if(childCount > 1){
            child = myRoot.getChild(1).getText();
            if(child.equals(";"))
                processStmt(ansPG, myRoot, fromNode, toNode, cond, post_np);
        }
        else
            PGFromNP(ansPG, myRoot.getChild(0), fromNode, toNode, cond, post_np);
    }

    private void processIf(ProgramGraph<String, String> ansPG, ParseTree myRoot, String fromNode, String toNode, String cond, String post_np){
        int rootChildNum = myRoot.getChildCount() - 1;
        String ansCond, bracketsCond, ifCond;
        ParseTree child;

        for(int i = 1; i < rootChildNum; i++){
            child = myRoot.getChild(i).getChild(3);
            bracketsCond = "(" + cond + ")";
            ifCond = "(" + myRoot.getChild(i).getChild(1).getText() + ")";

            if(bracketsCond.equals("()"))
                ansCond = ifCond;
            else if(ifCond.equals("()"))
                ansCond = bracketsCond;
            else
                ansCond = bracketsCond + " && " + ifCond;

            PGFromNP(ansPG, child, fromNode, toNode, ansCond, post_np);
        }
    }

    private <L, A> void processDo(ProgramGraph<String, String> ansPG, ParseTree myRoot, String fromNode, String toNode, String cond, String post_np){
        int rootChildNum = myRoot.getChildCount() - 1;
        String ansCond, fromTransAns, rootTXT = myRoot.getText(), from_trans3 = toNode + post_np, consitionTransAns, doConds = "", switchedCond, finishDoCond = "";

        for(int i = 1; i < rootChildNum; i++){
            DoHelper(ansPG, myRoot, fromNode, toNode, cond, post_np, i);
            ansCond = myRoot.getChild(i).getChild(1).getText();
            switchedCond = switchCondition(ansCond);
            finishDoCond = finishDoCond + switchedCond + " && ";
            doConds = doConds + "(" + ansCond + ") || ";
        }
        doConds = doConds.substring(0, doConds.length() - 4);
        finishDoCond = finishDoCond.substring(0, finishDoCond.length() - 4);

        if(rootTXT.equals("") || rootTXT.equals("()")) fromTransAns = from_trans3;
        else if(from_trans3.equals("") || from_trans3.equals("()")) fromTransAns = rootTXT;
        else fromTransAns = rootTXT + ";" + from_trans3;

        if(cond.equals("") || cond.equals("()")) consitionTransAns = finishDoCond;
        else if(finishDoCond.equals("")) consitionTransAns = cond;
        else consitionTransAns = cond + " && (!(" + doConds + "))";

        PGTransition<L, A> trans_pg = new PGTransition<>((L)fromTransAns, finishDoCond, (A) "", (L)(toNode + post_np));
        ((ProgramGraph<L, A>) ansPG).addLocation(trans_pg.getFrom());
        ((ProgramGraph<L, A>) ansPG).addLocation(trans_pg.getTo());
        ((ProgramGraph<L, A>) ansPG).addTransition(trans_pg);

        PGTransition<L, A> trans_pg1 = new PGTransition<>((L)fromNode, consitionTransAns, (A) "", (L)(toNode + post_np));
        ((ProgramGraph<L, A>) ansPG).addLocation(trans_pg1.getFrom());
        ((ProgramGraph<L, A>) ansPG).addLocation(trans_pg1.getTo());
        ((ProgramGraph<L, A>) ansPG).addTransition(trans_pg1);
    }

    private String switchCondition(String cond){
        StringBuilder SB = new StringBuilder();

        for(int i = 0; i < cond.length(); i++){
            if(cond.charAt(i) == '>' && cond.charAt(i + 1) == '='){
                SB.append('<');
                i++;
            }
            else if(cond.charAt(i) == '<' && cond.charAt(i + 1) == '='){
                SB.append('>');
                i++;
            }
            else if(cond.charAt(i) == '>')
                SB.append("<=");
            else if(cond.charAt(i) == '<')
                SB.append(">=");
            else if(cond.charAt(i) == '=' && cond.charAt(i + 1) == '='){
                SB.append("!=");
                i++;
            }
            else if(cond.charAt(i) == 't' && cond.charAt(i + 1) == 'r' && cond.charAt(i + 2) == 'u' && cond.charAt(i + 3) == 'e'){
                SB.append("!true");
                i += 3;
            }
            else SB.append(cond.charAt(i));
        }
        return SB.toString();
    }

    private void DoHelper(ProgramGraph<String, String> ansPG, ParseTree myRoot, String fromNode, String toNode, String cond, String post_np, int i){
        String ansCond = myRoot.getChild(i).getChild(1).getText();
        ParseTree child = myRoot.getChild(i).getChild(3);
        String rootTXT = myRoot.getText(), ansPost, bracketsCond, cond3, ansCondUpdate, ansFrom, ansFromFinal;

        if(rootTXT.equals("") || rootTXT.equals("()")) ansPost = post_np;
        else if(post_np.equals("") || post_np.equals("()")) ansPost = rootTXT;
        else ansPost = rootTXT + ";" + post_np;

        bracketsCond = "(" + cond + ")";
        cond3 = "(" + ansCond + ")";
        if(bracketsCond.equals("()")) ansCondUpdate = cond3;
        else if(cond3.equals("()")) ansCondUpdate = bracketsCond;
        else ansCondUpdate = cond + " && (" + cond3 + ")";

        if(rootTXT.equals("") || rootTXT.equals("()")) ansFrom = toNode;
        else if(toNode.equals("") || toNode.equals("()")) ansFrom = rootTXT;
        else ansFrom = rootTXT + ";" + toNode;

        if(ansFrom.equals("") || ansFrom.equals("()")) ansFromFinal = post_np;
        else if(post_np.equals("") || post_np.equals("()")) ansFromFinal = ansFrom;
        else ansFromFinal = ansFrom + ";" + post_np;

        PGFromNP(ansPG, child, fromNode, toNode, ansCondUpdate, ansPost);
        PGFromNP(ansPG, child, ansFromFinal, toNode, cond3, ansPost);
    }

    private <L, A> void processOtherCase(ProgramGraph<String, String> ansPG, ParseTree myRoot, String fromNode, String toNode, String cond, String post_np) {
        String to_ans;

        if(toNode.equals("") || toNode.equals("()")) to_ans = post_np;
        else if(post_np.equals("") || post_np.equals("()")) to_ans = toNode;
        else to_ans = toNode + ";" + post_np;

        PGTransition<L, A> trans_pg = new PGTransition<>((L)fromNode, cond, (A)myRoot.getText(), (L)to_ans);
        ((ProgramGraph<L, A>) ansPG).addLocation(trans_pg.getFrom());
        ((ProgramGraph<L, A>) ansPG).addLocation(trans_pg.getTo());
        ((ProgramGraph<L, A>) ansPG).addTransition(trans_pg);
    }

    private void processStmt(ProgramGraph<String, String> ansPG, ParseTree myRoot, String fromNode, String toNode, String cond, String post_np){
        ParseTree child0 = myRoot.getChild(0), child2 = myRoot.getChild(2);
        String child2TXT = child2.getText(), ansPost;

        if(child2TXT.equals("") || child2TXT.equals("()")) ansPost = post_np;
        else if(post_np.equals("") || post_np.equals("()")) ansPost = child2TXT;
        else ansPost = child2TXT + ";" + post_np;

        PGFromNP(ansPG, child0, fromNode, toNode, cond, ansPost);
        PGFromNP(ansPG, child2, ansPost, toNode, "", post_np);
    }



    private ProgramGraph<String, String> getPGfromStmt(NanoPromelaParser.StmtContext root) {
        ProgramGraph<String, String> newPG = new ProgramGraphImpl<>();
        Set<String> locs = sub(newPG, root);
        //LOCATIONS
        for (String loc : locs) {
            newPG.addLocation(loc);
        }
        newPG.setInitial(root.getText(), true);

        //delete unreachable locs.
        Set<String> reachables = pgReach(newPG);
        Set<String> nonreachables = new HashSet<>();
        for (String locs2 : newPG.getLocations()) {
            if (!reachables.contains(locs2)) {
                nonreachables.add(locs2);
            }
        }

        for (String locs3 : nonreachables) {
            newPG.removeLocation(locs3);
        }
        Set<PGTransition<String, String>> toRemove = new HashSet<>();
        for (PGTransition<String, String> trans : newPG.getTransitions()) {
            if (!newPG.getLocations().contains(trans.getTo())) {
                toRemove.add(trans);
            }
            if (!newPG.getLocations().contains(trans.getFrom())) {
                toRemove.add(trans);
            }
        }
        for (PGTransition<String, String> trans : toRemove) {
            newPG.removeTransition(trans);
        }

        return newPG;
    }

    private Set<String> pgReach(ProgramGraph<String, String> pg) {
        Set<String> reachableStates = new HashSet<>();
        for (String initialState : pg.getInitialLocations()) {
            reachableStates.add(initialState);
            pgReach(initialState, pg, reachableStates);
        }
        reachableStates.addAll(pg.getInitialLocations());
        return reachableStates;
    }

    private void pgReach(String init, ProgramGraph<String, String> pg, Set<String> reachableStates) {
        for (PGTransition<String, String> transition : pg.getTransitions()) {
            if (transition.getFrom().equals(init)) {
                if (!reachableStates.contains(transition.getTo())) {
                    reachableStates.add(transition.getTo());
                    pgReach(transition.getTo(), pg, reachableStates);
                }
            }
        }
    }

    private Set<String> sub(ProgramGraph<String, String> newPG, NanoPromelaParser.StmtContext root) {
        Set<String> locs = new HashSet<>();
        if (root.assstmt() != null || root.chanreadstmt() != null || root.chanwritestmt() != null || root.atomicstmt() != null || root.skipstmt() != null) {
            locs.add(root.getText());
            locs.add("");
            newPG.addTransition(new PGTransition<>(root.getText(), "", root.getText(), ""));
        } else if (root.ifstmt() != null) {
            locs.add(root.ifstmt().getText());
            locs.add("");
            for (NanoPromelaParser.OptionContext op : root.ifstmt().option()) {
                Set<String> ifSub = sub(newPG, op.stmt());
                locs.addAll(ifSub);
                Set<PGTransition<String, String>> toAdd = new HashSet<>();
                for (PGTransition<String, String> trans : newPG.getTransitions()) {
                    if (trans.getFrom().equals(op.stmt().getText())) {
                        String newCond = trans.getCondition().equals("") ||
                                trans.getCondition().equals("true") ?
                                '(' + op.boolexpr().getText() + ')' :
                                '(' + op.boolexpr().getText() + ") && (" + trans.getCondition() + ')';
                        PGTransition<String, String> newTrans = new PGTransition<>(root.ifstmt().getText(), newCond, trans.getAction(), trans.getTo());
                        toAdd.add(newTrans);
                    }
                }
                for (PGTransition<String, String> trans : toAdd) {
                    newPG.addTransition(trans);
                }
            }
        } else if (root.dostmt() != null) {
            locs.add(root.dostmt().getText());
            locs.add("");
            StringBuilder notCond = new StringBuilder();
            notCond.append("!(");
            List<NanoPromelaParser.OptionContext> optionList = root.dostmt().option();
            for (NanoPromelaParser.OptionContext op : optionList) {
                Set<String> newLocs = sub(newPG, op.stmt());
                newLocs.remove("");
                for (String dosub : newLocs) {
                    String doSubAdd = dosub + ';' + root.dostmt().getText();
                    locs.add(doSubAdd);
                    Set<PGTransition<String, String>> toAdd = new HashSet<>();

                    if (op.equals(optionList.get(optionList.size() - 1))) {
                        notCond.append('(').append(op.boolexpr().getText()).append("))");
                    } else {
                        notCond.append('(').append(op.boolexpr().getText()).append(")||");
                    }

                    for (PGTransition<String, String> trans : newPG.getTransitions()) {
                        String to, cond;
                        if (dosub.equals(trans.getFrom())) {
                            if (trans.getTo().equals("")) {
                                to = root.dostmt().getText();
                            } else {
                                to = trans.getTo() + ';' + root.dostmt().getText();
                            }
                            toAdd.add(new PGTransition<>(dosub + ';' + root.dostmt().getText(), trans.getCondition(), trans.getAction(), to));
                        }

                        if (op.stmt().getText().equals(trans.getFrom())) {
                            if (trans.getTo().equals("")) {
                                to = root.dostmt().getText();
                            } else {
                                to = trans.getTo() + ';' + root.dostmt().getText();
                            }
                            if (trans.getCondition().equals("") || trans.getCondition().contains("true")) {
                                cond = '(' + op.boolexpr().getText() + ')';
                            } else {
                                cond = '(' + op.boolexpr().getText() + ") && (" + trans.getCondition() + ')';
                            }
                            toAdd.add(new PGTransition<>(root.dostmt().getText(), cond, trans.getAction(), to));
                        }
                    }
                    for (PGTransition<String, String> trans : toAdd) {
                        newPG.addTransition(trans);
                    }
                }
            }
            newPG.addTransition(new PGTransition<>(root.dostmt().getText(), notCond.toString(), "", ""));
        } else {
            locs.add(root.getText());
            Set<String> newLocs = sub(newPG, root.stmt(1));
            locs.addAll(newLocs);

            Set<String> subs0 = sub(newPG, root.stmt(0));
            subs0.remove("");
            for (String s : subs0) {
                String locToAdd = s + ';' + root.stmt(1).getText();
                locs.add(locToAdd);
                Set<PGTransition<String, String>> toAdd = new HashSet<>();
                for(PGTransition<String, String> trans : newPG.getTransitions()) {
                    String to;
                    if (s.equals(trans.getFrom())) {
                        if(trans.getTo().equals("")){
                            to = root.stmt(1).getText();
                        }
                        else{
                            to = trans.getTo() + ';' + root.stmt(1).getText();
                        }
                        toAdd.add(new PGTransition<>(locToAdd, trans.getCondition(), trans.getAction(), to));
                    }
                }
                for (PGTransition<String, String> trans : toAdd) {
                    newPG.addTransition(trans);
                }
            }
        }
        return locs;
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        TransitionSystem<Pair<Sts,Saut>, A, Saut> ans = new TransitionSystemImpl<>();

        //S
        for(Sts sts : ts.getStates()){
            for(Saut saut : aut.getTransitions().keySet()){
                ans.addState(new Pair<>(sts, saut));
            }
        }

        //ACT
        ans.addAllActions(ts.getActions());

        //->
        for(Pair<Sts, Saut> uno : ans.getStates()){
            for(Pair<Sts, Saut> dos : ans.getStates()){
                Sts firstTS = uno.getFirst();
                Sts secondTS = dos.getFirst();
                Saut firstAut = uno.getSecond();
                Saut secondAut = dos.getSecond();
                A act = null;
                boolean isIn = false;

                for(Transition<Sts, A> transition : ts.getTransitions()){
                    if(transition.getFrom().equals(firstTS) && transition.getTo().equals(secondTS)){
                        act = transition.getAction();
                    }
                }


                Set<Saut> sauts = aut.getTransitions().get(firstAut).get(ts.getLabel(secondTS));
                if(sauts != null && sauts.contains(secondAut)){
                    isIn = true;
                }

                if(act!= null && isIn){
                    ans.addTransition(new Transition<>(uno, act, dos));
                }
            }
        }
        //I
        for(Sts sts : ts.getInitialStates()){
            Set<P> aps = ts.getLabel(sts);
            for(Saut saut : aut.getInitialStates()){
                Set<Saut> lamda = aut.getTransitions().get(saut).get(aps);
                for(Saut saut1 : lamda){
                    ans.setInitial(new Pair<Sts, Saut>(sts, saut1), true);
                }
            }
        }
        //AP
        ans.addAllAtomicPropositions(aut.getTransitions().keySet());
        //L
        for(Pair<Sts, Saut> pair : ans.getStates()){
            ans.addToLabel(pair, pair.getSecond());
        }


        //remove unreachable states
        Set<Pair<Sts, Saut>> reachableStates = reach(ans);
        Set<Pair<Sts, Saut>> toRemove = new HashSet<>();
        for(Pair<Sts, Saut> pair : ans.getStates()){
            if(!reachableStates.contains(pair)){
                toRemove.add(pair);
            }
        }

        for(Pair<Sts, Saut> pair : toRemove){
            Set<Transition<Pair<Sts, Saut>, A>> transitionsToRemove = new HashSet<>();
            for (Transition<Pair<Sts, Saut>, A> transition : ans.getTransitions()) {
                if (transition.getFrom().equals(pair) || transition.getTo().equals(pair)) {
                    transitionsToRemove.add(transition);
                }
            }
            for(Transition<Pair<Sts,Saut>, A> transition : transitionsToRemove){
                ans.removeTransition(transition);
            }
            Set<Saut> labels = ans.getLabel(pair);
            for(Saut label : labels){
                ans.removeLabel(pair, label);
            }
            if(ans.getInitialStates().contains(pair)){
                ans.setInitial(pair, false);
            }
            ans.removeState(pair);
        }
        Set<Saut> apToRemove = new HashSet<>();
        for(Saut saut : ans.getAtomicPropositions()){
            Map<Pair<Sts, Saut>, Set<Saut>> labels = ans.getLabelingFunction();
            boolean isPresent = false;
            for(Set<Saut> sautSet : labels.values()){
                if(sautSet.contains(saut)){
                    isPresent = true;
                }
            }
            if(!isPresent){
                apToRemove.add(saut);
            }
        }
        for(Saut saut : apToRemove){
            ans.removeAtomicProposition(saut);
        }

        return ans;
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        TransitionSystem<Pair<S, Saut>, A, Saut> prod = product(ts, aut);
        Set<Saut> acceptingStates = aut.getAcceptingStates();
        Set<Pair<S, Saut>> r = new HashSet<>();
        Set<Pair<S, Saut>> rNot = new HashSet<>();
        Stack<Pair<S, Saut>> u = new Stack<>();
        Set<Pair<S, Saut>> t;
        Stack<Pair<S, Saut>> v;

        for (Pair<S, Saut> s : prod.getInitialStates()) { // TODO: Check if required I/R instead of I
            visit(prod, acceptingStates, r, rNot, u, s);
        }
        for (Pair<S, Saut> s : rNot) {
            t = new HashSet<>();
            v = new Stack<>();
            List<S> cycle = cycleCheck(prod, t, v, s);
            if (!cycle.isEmpty()) {
                VerificationFailed<S> vr = new VerificationFailed<>();
                List<S> prefix = new LinkedList<>();
                for (Pair<S, Saut> i : prod.getInitialStates()) { // TODO: Check if required I/R instead of I
                    prefix = getPrefix(prod, i, s);
                    if (!prefix.isEmpty()) {
                        break;
                    }
                }
                vr.setCycle(cycle);
                vr.setPrefix(prefix);
                return vr;
            }
        }
        return new VerificationSucceeded<>();
    }

    private <S, A, Saut> List<S> getPrefix(
            TransitionSystem<Pair<S, Saut>, A, Saut> prod,
            Pair<S, Saut> i,
            Pair<S, Saut> s) {
        Set<Pair<S, Saut>> r = new HashSet<>();
        Stack<Pair<S, Saut>> u = new Stack<>();
        List<S> prefix = new LinkedList<>();
        u.push(i);
        r.add(i);
        do {
            Pair<S, Saut> st = u.peek();
            if (r.containsAll(post(prod, st))) {
                u.pop();
                if (st.equals(s)) {
                    //Found S
                    Stack<Pair<S, Saut>> reversed = reverse(u);
                    while (!reversed.empty()) {
                        prefix.add(reversed.pop().first);
                    }
                    return prefix;
                }
            }
            else {
                Pair<S, Saut> stt = minus(post(prod, st), r);
                u.push(stt);
                r.add(stt);
            }
        } while (!u.empty());
        return prefix;
    }

    private <T> Stack<T> reverse(Stack<T> s) {
        Stack<T> reversed = new Stack<>();
        while (!s.empty()) {
            reversed.push(s.pop());
        }
        return reversed;
    }

    private <S, A, Saut> void visit(
            TransitionSystem<Pair<S, Saut>, A, Saut> prod,
            Set<Saut> acceptingStates,
            Set<Pair<S, Saut>> r,
            Set<Pair<S, Saut>> rNot,
            Stack<Pair<S, Saut>> u,
            Pair<S, Saut> s) {
        u.push(s);
        r.add(s);
        do {
            Pair<S, Saut> st = u.peek();
            if (r.containsAll(post(prod, st))) {
                u.pop();
                if (acceptingStates.contains(st.getSecond())) {
                    rNot.add(st);
                }
            }
            else {
                Pair<S, Saut> stt = minus(post(prod, st), r);
                u.push(stt);
                r.add(stt);
            }
        } while (!u.empty());
    }

    private <S, A, Saut> List<S> cycleCheck(
            TransitionSystem<Pair<S, Saut>, A, Saut> prod,
            Set<Pair<S, Saut>> t,
            Stack<Pair<S, Saut>> v,
            Pair<S, Saut> s) {
        List<S> cycle = new ArrayList<>();
        boolean cycleFound = false;
        v.push(s);
        t.add(s);
        do {
            Pair<S, Saut> st = v.peek();
            if (post(prod, st).contains(s)) {
                Stack<Pair<S, Saut>> reversed = reverse(v);
                while (!reversed.empty()) {
                    cycle.add(reversed.pop().first);
                }
                cycleFound = true;
            }
            else {
                if (minus(post(prod, st), t) != null) {
                    Pair<S, Saut> stt = minus(post(prod, st), t);
                    v.push(stt);
                    t.add(stt);
                }
                else {
                    v.pop();
                }
            }
        }
        while (!v.empty() && !cycleFound);
        return cycle;
    }

    /**
     * Assumes set1 contains exactly 1 element more than s2. Returns it.
     * @param set1
     * @param set2
     * @param <S>
     * @param <A>
     * @param <Saut>
     * @return
     */
    private <S, A, Saut> Pair<S, Saut> minus(Set<Pair<S, Saut>> set1, Set<Pair<S, Saut>> set2) {
        for (Pair<S, Saut> s : set1) {
            if (!set2.contains(s)) {
                return s;
            }
        }
        return null;
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
