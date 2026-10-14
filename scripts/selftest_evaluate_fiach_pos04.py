#!/usr/bin/env python3
"""In-memory group-sensitivity probes, not exhaustive obligation isolation."""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path

import evaluate_fiach_pos04 as ev


MODEL=ev.ROOT/'audit/proposed_models/FIACH-POS-04.model.json'
PREDICTIONS=ev.ROOT/'audit/M3_predictions.md'


def declared_negative(model, mid):
    return ev.mutate(model, next(x for x in model['mutations'] if x['id']==mid))


def raw_row(model):
    model['new_data']['raw_inputs']['by_tag']['target']['action_distributions']['p0w0']['stay']={
        'p1w0':'1/1'}


def public_identity(model):
    for tag in ev.TAGS:
        model['new_data']['raw_inputs']['by_tag'][tag]['public_channel_rule']='state_label'


def no_source(model):
    model['new_data']['receiver']['activation']['source_present']=False


def unrealize(model):
    model['new_data']['corridor']['realized_stages'].remove('mix_1')


def nonstrict(model):
    model['new_data']['corridor']['events'][0]['strict_step']=False


def invalid_history(model,name):
    model['new_data']['histories'][name]=['p1w0','p1w0','p1w0']


def missing_route_context(model):
    del model['new_data']['raw_inputs']['by_tag']['target']['record_writer_available']['route_b']


def reordered_stages(model):
    model['new_data']['corridor']['realized_stages']=['source_live','mix_2','mix_1','target_exit']


def no_recharge(model):
    model['new_data']['raw_inputs']['by_tag']['target']['resources']['recharge_available_after_withdrawal']=False


def no_register(model):
    model['new_data']['receiver']['route_register_write']['rule']='constant_none'


def identity_p(model):
    n=len(model['t1_import']['kernel_order'])
    model['t1_import']['P']=[['1/1' if i==j else '0/1' for j in range(n)] for i in range(n)]


def corrupt_provenance(model):
    model['provenance']['imported_tables']['P']['sha256_lines']='0'*64


def missing_coordinate(model):
    model['new_data']['local_assignments'].pop()


def missing_intervention(model):
    model['mutations'].pop()


def unknown_event_stage(model):
    model['new_data']['corridor']['events'][0]['from']='unlisted_stage'


def broken_transport(model):
    return declared_negative(model,'NEG-C7-TRANSPORT')


def broken_coupling(model):
    return declared_negative(model,'NEG-C7-UNCOUPLED')


def broken_c5(model):
    return declared_negative(model,'NEG-C5-EXTERNAL')


def evaluate_mutation_target(model):
    variant=declared_negative(model,'NEG-C7-UNCOUPLED')
    original=model['new_data']['c7']['by_tag']['source']['assemblages'][1]['coupling']
    variant['new_data']['c7']['by_tag']['source']['assemblages'][1]['coupling']=copy.deepcopy(original)
    return variant


def positive(model):
    return ev.positive_rows(model,ev.evaluate(model))


def check_lean_mismatch(model):
    try:
        ev.lean_crosscheck(ev.evaluate(model))
    except RuntimeError as error:
        return 'BLOCKING: Python/Lean C1 mismatch' in str(error)
    return False


def check_bad_pointer(model):
    try:
        ev.mutate(model,{'changes':[{'op':'replace','path':'/new_data/missing','value':False}]})
    except ValueError:
        return True
    return False


def cases():
    # One direct failure probe for each of the thirty checks in coverage_index.
    return [
      ('T1 provenance hashes','corrupt pinned P span hash',corrupt_provenance,
       lambda m:not ev.provenance_check(m)['pass']),
      ('Tagged canonical P and M from raw actions','change target canonical action row',raw_row,
       lambda m:ev.canonical_matrix(m,'target')!=ev.fraction_matrix(m['t1_import']['P'])),
      ('C1 C/U, E₂ε, fixed law, retention, TV, defects','change target canonical action row',raw_row,
       lambda m:not ev.c1(m,'target')['pass']),
      ('C1 uniqueness for all normalized fixed laws','replace raw published P by identity matrix',identity_p,
       lambda m:not ev.fixed_law(ev.fraction_matrix(m['t1_import']['P']))['unique']),
      ('C1 agreement with Lean theorems and axioms','change target canonical action row',raw_row,
       check_lean_mismatch),
      ('C2 split and pinned witness','make public readout state-identifying',public_identity,
       lambda m:not ev.c2(m,'target')['pass']),
      ('C3 recursive action/exit profile and terminal M','make initial public partition discrete',public_identity,
       lambda m:not ev.c3(m,'target')['pass']),
      ('C4 full current family and hidden connector','add canonical M public reader',
       lambda m:m['new_data']['c4']['current_channels'].append('canonical_M'),
       lambda m:not ev.c4(m,'target')['pass']),
      ('C5 forward/reverse products, credit and anchors','externalize native target protocol',broken_c5,
       lambda m:not ev.c5(m,'target')['pass']),
      ('C6 full interface and all-word fixed point','change merged member tick response',
       lambda m:declared_negative(m,'NEG-C6-FUTURE'),
       lambda m:not ev.c6(m,'target')['pass']),
      ('C6 funded order/tick/record and owner','unset first event strict_step',nonstrict,
       lambda m:not ev.c6_trace(m,'target')['pass']),
      ('C7 per-assemblage reassembly and strict refinement','equalize both raw couplings',broken_coupling,
       lambda m:not ev.c7_local(m,'target')['pass']),
      ('C7 receiver pre-exit jointPairing display','remove source presence',no_source,
       lambda m:not ev.c7_receiver_display(m,'target')['pass']),
      ('C7 staged joint relation preservation','change target coupling and reassembly',broken_transport,
       lambda m:not ev.c7_transport(m)['pass']),
      ('C8 priced ledger, gfp and canonical P','remove target recharge',no_recharge,
       lambda m:not ev.c8(m,'target')['pass']),
      ('T1 histories, strict edge and bridge laws','override one representative endpoint',
       lambda m:declared_negative(m,'NEG-BRIDGE-REP'),
       lambda m:not ev.bridge(m)['pass']),
      ('Source-absent activation','remove source input from positive receiver',no_source,
       lambda m:not ev.receiver_active(m)),
      ('Raw-coordinate receiver and content counterfactuals','replace content by preloaded copy',
       lambda m:declared_negative(m,'NEG-PRELOADED-COPY'),
       lambda m:not ev.content(m)['pass']),
      ('Mixed corridor, no gap and support interventions','unrealize mix_1',unrealize,
       lambda m:not ev.corridor(m)['pass']),
      ('Funded target step and persistent route readout','delete target register write',no_register,
       lambda m:not ev.route(m)['pass']),
      ('Typed corridor/receiver endpoint link','override representative target endpoint',
       lambda m:declared_negative(m,'NEG-BRIDGE-REP'),
       lambda m:not ev.evaluate(m)['typed_endpoint_link']['pass']),
      ('160 state-indexed package coordinates','delete one target clause coordinate',missing_coordinate,
       lambda m:not ev.package_coordinates(m)['pass']),
      ('Eight staged maps and raw clause equations','alter one target C5 raw protocol',
       lambda m:declared_negative(m,'NEG-C5-INTERNALIZED'),
       lambda m:not ev.staged(m,{'clauses':ev.evaluate(m)['clauses']})['pass']),
      ('Source-removed target-only C8 autonomy','keep source available after withdrawal',
       lambda m:m['new_data']['maintenance'].__setitem__('source_available_after_withdrawal',True),
       lambda m:not ev.target_only_autonomy(m)['pass']),
      ('TTH-06 surrogate assembly','remove source input',no_source,
       lambda m:not ev.evaluate(m)['handoff']['pass']),
      ('References, distributions, reassembly and events','give an event an unknown source stage',unknown_event_stage,
       lambda m:not ev.check_wellformed(m)['pass']),
      ('Unchanged JSON-Pointer intervention semantics','replace a nonexistent raw path',lambda m:None,
       check_bad_pointer),
      ('Positive prediction coverage and gates','remove source input',no_source,
       lambda m:positive(m)['C7 joint refinement and transport']['pass'] is False),
      ('Mutation targets and outcome categories','undo source half of uncoupled control',
       evaluate_mutation_target,
       lambda m:not ev.mutation_target('NEG-C7-UNCOUPLED',{},ev.evaluate(m),m)[0] and
                ev.classify_mutation('NEG-C7-UNCOUPLED',False,
                    ev.evaluate(m)['wellformed']['pass'],{},ev.evaluate(m))=='INVALID-CONTROL'),
      ('Exact prediction-list and mutation coverage','delete one declared intervention',
       missing_intervention,
       lambda m:not ev.prediction_coverage(m,positive(json.loads(MODEL.read_text())),PREDICTIONS)),
    ]


def run_selftest():
    base=json.loads(MODEL.read_text())
    listed=[x['check'] for x in ev.coverage_index()]
    suite=cases()
    if [name for name,_,_,_ in suite]!=listed:
        raise AssertionError('self-test cases do not match the complete coverage index')
    rows=[]
    for name,description,change,condition in suite:
        model=copy.deepcopy(base)
        changed=change(model)
        if changed is not None:model=changed
        failed=bool(condition(model))
        rows.append({'check':name,'perturbation':description,
                     'result':'CAUGHT' if failed else 'MISSED'})
    for name,description,change,condition in [
        ('C7 realized mixed event','unrealize mix_1 and mix_2',
         lambda m:m['new_data']['corridor'].__setitem__('realized_stages',['source_live','target_exit']),
         lambda m:not ev.c7_receiver_display(m,'target')['pass']),
        ('C7 funded receiver activation','remove receiver funding',
         lambda m:m['new_data']['receiver']['activation'].__setitem__('target_receiver_funded',False),
         lambda m:not ev.c7_receiver_display(m,'target')['pass']),
        ('C6 realized path','unrealize mix_1',unrealize,
         lambda m:not ev.c6_trace(m,'target')['pass'] and
                  not ev.c6_trace(m,'target')['realized_paths']),
        ('C6 realized order','reorder realized stage list',reordered_stages,
         lambda m:not ev.c6_trace(m,'target')['pass']),
        ('C6 route context availability','delete route_b writer',missing_route_context,
         lambda m:not ev.c6(m,'target')['pass'] and
                  not ev.c6(m,'target')['route_contexts']),
        ('C5 anchor history availability','make h_rep_a a non-support path',
         lambda m:invalid_history(m,'h_rep_a'),
         lambda m:not ev.c5(m,'target')['pass'] and
                  not ev.c5(m,'target')['history_anchors_valid']),
        ('C7 branch history availability','make h_split a non-support path',
         lambda m:invalid_history(m,'h_split'),
         lambda m:not ev.c7_local(m,'target')['pass'] and
                  not ev.c7_local(m,'target')['branch_histories_admissible'])]:
        model=copy.deepcopy(base);change(model)
        rows.append({'check':name,'perturbation':description,
                     'result':'CAUGHT' if condition(model) else 'MISSED'})
    return rows


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--json',action='store_true')
    args=parser.parse_args()
    rows=run_selftest()
    if args.json:
        print(json.dumps(rows,sort_keys=True))
    else:
        print('Group-sensitivity probes only; CAUGHT does not establish exhaustive isolation.')
        print('The C1 identity-matrix row is a method-level fixed-law solver probe.')
        print('| Check | In-memory perturbation | Result |')
        print('|---|---|---|')
        for row in rows:print(f"| {row['check']} | {row['perturbation']} | {row['result']} |")
    if any(row['result']!='CAUGHT' for row in rows):raise SystemExit(1)


if __name__=='__main__':main()
