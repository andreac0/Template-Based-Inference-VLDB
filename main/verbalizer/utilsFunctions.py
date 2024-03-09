import json

'''
    :param entry: a rule in a .json file
'''
def split_condition_from_rule(entry):
    # split possible conditions from a rule
    try:
        # split head and rule
        try: 
            entry_rule = entry['rule'][:-1]
        except:
            entry_rule = entry
        if " :- " not in entry_rule:
            entry_rule = entry_rule.replace(":-",' :- ')
        if "), " not in entry_rule:
            entry_rule = entry_rule.replace("),",'), ')
        head_rule, body_rule = entry_rule.split(" :- ")[0], entry_rule.split(" :- ")[1]

        # identify which are atoms and which are conditions on variables
        possible_conditions = body_rule.split('), ')[1:]

        # if the rule is not a linear one without conditions
        # if possible_conditions:
        new_cond = list()
        new_rule = head_rule + ':-' + body_rule.split('),')[0] + '),'

        for i in range(len(possible_conditions)):
            # it is an atom
            if not ('=' in possible_conditions[i] or '>' in possible_conditions[i] or '<' in possible_conditions[i]):
                possible_conditions[i] = possible_conditions[i] + '),'
                new_rule += possible_conditions[i]

            # it is a condition
            else:
                new_cond.append(possible_conditions[i])

        try:
            # split multiple condition base on comma, but not when there is an operator
            if 'msum' not in new_cond[0]:
                possible_conditions = new_cond[0].split(',')
            else:
                possible_conditions = new_cond
        except:
            possible_conditions = []

        # fix rule string after split of conditions (different scenario might apply)
        if new_rule[-3:] == '),':
            new_rule = new_rule[:-3] + ').'
        if new_rule[-1] == ',':
            new_rule = new_rule[:-1] + '.'
        if new_rule[-3:] == ')).':
            new_rule = new_rule[:-3] + ').'

        new_cond = list()
        algebric = list()
        for cond in possible_conditions:
            if not ('+' in cond or '-' in cond or '*' in cond or '/' in cond or 'msum' in cond):
                if cond.startswith(" "):
                    new_cond.append(cond.replace(" ",""))
                else:
                    new_cond.append(cond)
            else:
                algebric.append(cond.replace(" ",""))
        return new_rule, new_cond, algebric
    except:
        return [], [], []

