#!/usr/bin/env python3
"""Separate G6b in-memory group sensitivity probes; never edit declarations."""
import copy
import json
from pathlib import Path
import sys
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parent))
import evaluate_tth06_lanes as e


def pointer(model,path,value):
    parts=path.strip('/').split('/');at=model
    for k in parts[:-1]:at=at[int(k)] if isinstance(at,list) else at[k]
    key=int(parts[-1]) if isinstance(at,list) else parts[-1]
    at[key]=copy.deepcopy(value)


def cell(model,name,value=None):
    family,_,tag=name.partition(':')
    model['assignment_edits'].append({'op':'remove_cell' if value is None else 'replace_cell',
                                    'cell':{'constructor':family,**({'tag':tag} if tag else {})},'value':value})


def run_selftests(model):
    base=e.evaluate(model)
    probes=[]
    def add(check,description,edit,selector):
        m=copy.deepcopy(model)
        try:
            edit(m); a=e.assignment(m)
            if check.startswith('P.'):
                result,b=e.package(m,a)
            elif check.startswith('L.'):
                result=e.lineage(m,a)
            else:
                # Recompute mapped/assigned package even for autonomy-only guards.
                P,b=e.package(m,a)
                result=e.autonomy(m,b,P,'F' if check.startswith('AF.') else 'O')
            got=bool(selector(result))
            caught=not got
            record={'check':check,'perturbation':description,'result':'CAUGHT' if caught else 'MISSED','observed':got}
            if check=='L.snapshot_afterFirst':
                record['witness']={'lineage':result['pass'],'snapshot_domain':result['bridge']['snapshot_domain'],
                                   'coordinate_checks':result['bridge']['snapshot_coordinate_checks']}
            elif check.startswith('L.declared_route_'):
                record['witness']={'lineage':result['pass'],'readout_spec':result['route']['readout_spec'],
                                   'readouts':[x['future_readout'] for x in result['route']['records']]}
            elif check.endswith(('.arrival_activation','.arrival_realization')):
                record['witness']={'autonomy':result['pass'],'arrival_execution':result['gates']['arrival_execution'],
                                   'entry_states':result['entry_states']}
            probes.append(record)
        except Exception as error:
            probes.append({'check':check,'perturbation':description,'result':'ERROR','error':f'{type(error).__name__}: {error}'})
    leaf=lambda r:r['pass']
    add('P.totality','remove shared publishedC cell',lambda m:cell(m,'publishedC'),lambda r:r['gates']['map_total'])
    add('P.C1','change a canonical source row probability from 1/2 to 1/4 and its partner to 3/4',
        lambda m:(pointer(m,'/base/new_data/raw_inputs/by_tag/source/action_distributions/p0w0/stay/p1w0','1/4'),
                  pointer(m,'/base/new_data/raw_inputs/by_tag/source/action_distributions/p0w0/stay/p1w1','3/4')),
        lambda r:r['clauses']['target']['C1']['pass'])
    add('P.C2','source lower readout becomes state_label (maps to target)',lambda m:cell(m,'lower:source','state_label'),lambda r:r['clauses']['target']['C2']['pass'])
    add('P.C3','source lower readout becomes state_label (maps to target)',lambda m:cell(m,'lower:source','state_label'),lambda r:r['clauses']['target']['C3']['pass'])
    add('P.C4','add canonical_M to shared current channels',lambda m:cell(m,'channels',['public_position','deadline_action_availability','canonical_M']),lambda r:r['clauses']['target']['C4']['pass'])
    add('P.C5','remove all source clockwise generator edges',lambda m:pointer(m,'/base/new_data/c5/protocols/0/edges',[]),lambda r:r['clauses']['target']['C5']['pass'])
    add('P.C6','remove mix_1 from realized stage list',lambda m:pointer(m,'/base/new_data/corridor/realized_stages',['source_live','mix_2','target_exit']),lambda r:r['clauses']['target']['C6']['pass'])
    add('P.C7','remove source-present activation',lambda m:pointer(m,'/base/new_data/receiver/activation/source_present',False),lambda r:r['clauses']['target']['C7']['pass'])
    add('P.C8','source recharge unavailable (maps to target)',lambda m:pointer(m,'/base/new_data/raw_inputs/by_tag/source/resources/recharge_available_after_withdrawal',False),lambda r:r['clauses']['target']['C8']['pass'])
    add('L.realization','un-realize mix_1',lambda m:pointer(m,'/base/new_data/corridor/realized_stages',['source_live','mix_2','target_exit']),leaf)
    add('L.audit','delete mix_2 source support only',lambda m:pointer(m,'/base/new_data/corridor/events/1/source_support',False),lambda r:r['atomic']['pass'])
    add('L.strict_step','set mix_1 strict_step false',lambda m:pointer(m,'/base/new_data/corridor/events/0/strict_step',False),leaf)
    add('L.full_future','set source p0w0/stay tick to 2; p0w1 stays 1',lambda m:pointer(m,'/base/new_data/raw_inputs/by_tag/source/tick_increment/p0w0/stay',2),lambda r:r['bridge']['gates']['full_future'])
    add('L.record','disable target route_a writer',lambda m:pointer(m,'/base/new_data/raw_inputs/by_tag/target/record_writer_available/route_a',False),leaf)
    add('L.representatives','replace second representative history with first raw history',lambda m:pointer(m,'/base/new_data/histories/h_rep_b',m['base']['new_data']['histories']['h_rep_a']),lambda r:r['bridge']['gates']['different_pasts'])
    add('L.route','erase raw register write',lambda m:pointer(m,'/base/new_data/receiver/route_register_write/rule','erase'),lambda r:r['route']['pass'])
    add('L.activation','source absent at receiver',lambda m:pointer(m,'/base/new_data/receiver/activation/source_present',False),leaf)
    add('L.owner','target resource owned by source',lambda m:pointer(m,'/base/new_data/maintenance/owner_by_tag/target','source'),leaf)
    add('L.snapshot_afterFirst','constant-position receiver keeps terminal p1 but corrupts both intermediate snapshot maps',
        lambda m:pointer(m,'/base/new_data/receiver/content/position_rule','constant_1'),
        lambda r:r['pass'] or r['bridge']['gates']['snapshot_coordinate_map'])
    add('L.declared_route_readout','change the declared future readout from first history phase to last',
        lambda m:pointer(m,'/base/new_data/corridor/future_route_readout/rule',
            'phase of last source WheelState in retained raw route tuple after one funded target step'),
        lambda r:r['pass'] or [x['future_readout'] for x in r['route']['records']]==
                             [x['future_readout'] for x in base['lineage']['route']['records']])
    add('L.declared_route_owner','make the declared route readout source-owned',
        lambda m:pointer(m,'/base/new_data/corridor/future_route_readout/owner','source'),
        lambda r:r['pass'] or r['route']['gates']['readout_owner'])

    for v in ('AF','AO'):
        add(v+'.arrival_activation','source_present false before arrival; independently require no entry and failed autonomy',
            lambda m:pointer(m,'/base/new_data/receiver/activation/source_present',False),
            lambda r:r['pass'] or r['gates']['arrival_execution'] or bool(r['entry_states']))
        add(v+'.arrival_realization','un-realize mix_1 before phase-2 execution; require no entries',
            lambda m:pointer(m,'/base/new_data/corridor/realized_stages',['source_live','mix_2','target_exit']),
            lambda r:r['pass'] or r['gates']['arrival_execution'] or bool(r['entry_states']))
        add(v+'.retention','retain no essential recharge resource',lambda m:pointer(m,'/declaration/raw_interface/post_exit_retention/retained_resources',[]),leaf)
        add(v+'.source_withdrawal','source remains present after withdrawal',lambda m:pointer(m,'/declaration/raw_interface/post_exit_retention/source_present_after_withdrawal',True),leaf)
        add(v+'.role_withdrawal','external scheduler not removed',lambda m:pointer(m,'/declaration/raw_interface/withdrawal_rule/removed_roles',['source','migration_bridge','migration_controller','external_decoder','undeclared_repair_support']),leaf)
        add(v+'.disturbance','empty disturbance domain',lambda m:pointer(m,'/declaration/raw_interface/disturbance_interface/domain',[]),leaf)
        add(v+'.ledger','zero budget, cost and recharge',lambda m:cell(m,'maintenance',{'initial_budget_tokens':0,'action_cost_tokens':0,'recharge_tokens_per_action':0}),leaf)
        add(v+'.record','disable source route_a writer (maps to target)',lambda m:pointer(m,'/base/new_data/raw_inputs/by_tag/source/record_writer_available/route_a',False),leaf)
        add(v+'.tick','set source p0w0/stay tick to zero (maps to target)',lambda m:pointer(m,'/base/new_data/raw_inputs/by_tag/source/tick_increment/p0w0/stay',0),leaf)
        add(v+'.owner','source resource owned by target (maps to wrong target owner)',lambda m:pointer(m,'/base/new_data/maintenance/owner_by_tag/source','target'),leaf)
        add(v+'.missing_dependency','delete shared routeTable cell',lambda m:cell(m,'routeTable'),leaf)
    add('AF.packageInside','remove shared publishedC cell',lambda m:cell(m,'publishedC'),leaf)
    # This verifies support safety itself: retain just p1w0; an escape is not a lucky response.
    m=copy.deepcopy(model);i=e.Inputs(m,e.exchange(e.assignment(m)))
    caught=not e.safe_actions(i,'target','p2w1',{'p1w0'})
    probes.append({'check':'AF/AO.full_support_safety','perturbation':'candidate invariant contains p1w0 but not p1w1; p2w1/stay has positive mass to both',
                   'result':'CAUGHT' if caught else 'MISSED','observed':not caught})
    # Regression for G3b's reporting lesson: self-test failure is separate.
    # No frozen input is changed; simulate unavailable self-test infrastructure.
    try:
        import selftest_evaluate_tth06_lanes as own_module
        with patch.object(own_module,'run_selftests',side_effect=RuntimeError('planted self-test failure')):
            reported=e.run(e.ROOT/'audit/proposed_models/TTH06-LANES.model.json')
        caught=(reported['selftest']['status']=='ERROR' and len(reported['predictions'])==24
                and bool(reported['cases']) and 'AF_implies_P' in reported)
        probes.append({'check':'reporting.selftest_failure','perturbation':'self-test raises while outcomes remain available',
                       'result':'CAUGHT' if caught else 'MISSED','observed':not caught})
    except Exception as error:
        probes.append({'check':'reporting.selftest_failure','perturbation':'self-test raises while outcomes remain available',
                       'result':'ERROR','error':f'{type(error).__name__}: {error}'})
    baseline=all(base['lane_vectors']['F'].values()) and all(base['lane_vectors']['O'].values())
    return {'status':'PASS' if baseline and all(p['result']=='CAUGHT' for p in probes) else 'FAIL',
            'method':'in-memory group sensitivity probes, not exhaustive isolation of every obligation',
            'baseline_available':baseline,'probes':probes,
            'counts':{x:sum(p['result']==x for p in probes) for x in ('CAUGHT','MISSED','ERROR')}}


def main():
    path=sys.argv[1] if len(sys.argv)>1 else 'audit/proposed_models/TTH06-LANES.model.json'
    result=run_selftests(e.load(path))
    print('Separate self-test status:',result['status']);print(result['method'])
    print('| Check | Perturbation | Result |');print('|---|---|---|')
    for p in result['probes']:print(f"| {p['check']} | {p['perturbation']} | {p['result']} |")
    print('Counts:',json.dumps(result['counts'],sort_keys=True))
    if result['status']!='PASS':sys.exit(1)

if __name__=='__main__':main()
