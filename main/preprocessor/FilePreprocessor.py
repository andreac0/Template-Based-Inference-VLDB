import json
import os
import logging
import re
import csv
from tqdm import tqdm
import pandas as pd

'''
    This class collects preprocessing and rewriting operations
    over input files to adapt them for the fine-tuning pipeline
    
    __author__: teodorobaldazzi
    __author__: andreacolombo
'''
class FilePreprocessor:

    logging.getLogger().setLevel(logging.INFO)



    '''
        :param node: the current node in the chase graph
        :param chase: the deserialized chase_file 
    '''
    def __get_children(self, node, chase):
        children = []
        
        for step in chase:
            if node['name'] in step['provenance']:
                children.append(step)

        return children
    


    '''
        :param step: a step of the chase
        :param chase: the deserialized chase_file 
        :param number: the current number in the hierarchical numbering
    '''
    def __number_chain(self, step, chase, number):

        if number not in step['number']:
            step['number'].append(number)

        num = 0
        num_t = 0

        for child in self.__get_children(step, chase):
            # print(child)
            if child['rule'] and not child['name'].startswith('vatom'):
                num += 1
                child_number = f"{number}.{num}"
            elif child['rule'] and child['name'].startswith('vatom'):
                num_t += 1
                child_number = f"{number}"+".T"+ str(num_t)
            else:
                child_number = number

            self.__number_chain(child, chase, child_number)

            if '.' not in number:
                number = str(int(number)+1)
        
        return number


    '''
        This method initializes the 'number' field in the chase_graph.json file
        
        :param chase_path: the path to the chase_graph.json file with the chase graph
    '''
    def __set_number_field_chase_graph(self, chase_path):
        try:
            with open(chase_path, "r") as c:
                # deserialize chase file
                chase = json.load(c)
                with open('temp_chase_graph.json', 'w') as nc:
                    first_step = True
                    nc.write('[')
                    # initialize the number field in the json
                    for step in chase:
                        nstep = {'name': step['name'],
                                 'pattern': step['pattern'],
                                 'provenance': step['provenance'],
                                 'rule': step['rule'],
                                 'number': []}
                        if first_step:
                            first_step = False
                        else:
                            nc.write('\n,')
                        json.dump(nstep, nc, separators=(",", ":"))
                    nc.write('\n]')
        except Exception as e:
            print(f"An error occurred: {e}")



    '''
        This method creates a .json file with the chase graph with hierarchical numbering,
        such that each chase step includes a number that links it to its ancestor steps
        
        :param chase_path: path to the chase_graph.json file with the chase graph
        :param output_path: path to output file
    '''
    def number_chase_graph(self, chase_path, output_path):
        try:
            self.__set_number_field_chase_graph(chase_path)
            with open("temp_chase_graph.json") as c:
                # deserialize chase file
                chase = json.load(c)
                with open(output_path + "num_chase_graph.json", "w") as nc:
                    first_step = True
                    
                    num = 0
                    for step in tqdm(chase):
                        if step['provenance'] == "[]":  # ground fact
                            # print(step)
                            num += 1
                            num = int(self.__number_chain(step, chase, str(num)))
                            

                    nc.write('[')
                    for step in chase:
                        nstep = {'name': step['name'],
                                 'pattern': step['pattern'],
                                 'provenance': step['provenance'],
                                 'rule': step['rule'],
                                 'number': step['number']}
                        if first_step:
                            first_step = False
                        else:
                            nc.write('\n,')
                        json.dump(nstep, nc, separators=(",", ":"))
                    nc.write('\n]')
            os.remove('temp_chase_graph.json')
        except Exception as e:
            print(f"An error occurred: {e}")

    def find_indexes(self, numbers, target):
        """
        Finds the indexes of the numbers in the list that sum to the target value.

        Args:
            numbers: A list of numbers.
            target: The target value.

        Returns:
            A list of the indexes of the numbers in the list that sum to the target value.
        """

        indexes = []
        for i in range(len(numbers)):
            for j in range(i + 1, len(numbers)):
                if numbers[i] + numbers[j] == target:
                    indexes.append(i)
                    indexes.append(j)
        return indexes

    def combination_contributors(self, provenance, rule, name):
        # print(name)
        # print(provenance)
        final_value_var = rule.split('=msum')[0].split(', ')[-1]
        head_var = rule.split(' :-')[0].split('(')[1].split(')')[0].split(',')
        name = name.split(' :-')[0].split('(')[1].split(')')[0].split(',')
        for i in range(len(head_var)):
            if head_var[i] == final_value_var:
                final_value = float(name[i])

        sum_variable = rule.split('msum(')[1].split(',')[0]
        predicate_var = rule.split(':- ')[1].split('),')[0].split('(')[1].split(',')
        if ')' in sum_variable:
            sum_variable = sum_variable.split(')')[0]
        for i in range(len(predicate_var)):
            if predicate_var[i] == sum_variable:
                index = i
        
        found = False
        sum_contributor = []
        for j in provenance:
            contr = float(j.split('(')[1].split(')')[0].split(',')[index])
            if contr == final_value:
                real_provenance = [j]
                found = True
                break
            sum_contributor.append(contr)

        if found == False:
            ind = self.find_indexes(sum_contributor, final_value)
            real_provenance = list()
            for k in ind:
                real_provenance.append(provenance[k])
        
        if real_provenance == []:
            return provenance
        return real_provenance

    '''
        This method creates a .json file with the chase graph updating the provenance of steps featuring aggregations
        to include all the contributors to the previous steps for that execution of the aggregation
        
        :param chase_path: the path to the chase_graph.json file with the chase graph
        :param output_path: path to output file
    '''
    def integrate_previous_contributors_to_aggregations(self, chase_path, output_path):
        try:
            with open(chase_path, 'r') as c:
                # deserialize chase file
                chase = json.load(c)

                # create new output file or rewrite existing one
                with open(output_path + "aggr_chase_graph.json", "w") as nc:
                    first_step = True
                    nc.write('[')

                    for step in tqdm(chase):
                        provenance = step['provenance']
                        if step['rule']:
                            # if a step features an aggregation in the rule (for now only msum is of interest to us)
                            # aggregationmatch = re.search(r" (\w)=msum\(.+?\)", step['rule'])
                            if 'msum' in step['rule']:
                                # print('\n')
                                # print(step['rule'])
                                # print(step['name'])
                                
                                aggregation = step['rule'].split(', ')[-1]
                                # get the variable storing the aggregate value from the aggregation
                                aggrarg = aggregation.split('=')[0]
                                # get the head atom in the rule
                                headatom = step['rule'][:-1].split(' :- ')[0]
                                # get the group by arguments and their position in the head atom
                                groupbyargs = re.findall(r'\((.*?)\)', headatom)[0]
                                groupbyargs_pos = {}
                                for i, arg in enumerate(groupbyargs.split(',')):
                                    if arg != aggrarg:
                                        groupbyargs_pos[i] = arg
                                # get the values in the generated fact corresponding to the group-by arguments
                                fact = step['name']
                                groupbyvalues = re.findall(r'\((.*?)\)', fact)[0]
                                groupbyvalues_pos = {}
                                for i, arg in enumerate(groupbyvalues.split(',')):
                                    if i in groupbyargs_pos:
                                        groupbyvalues_pos[i] = arg
                                # for each step in the chase up until the current one
                                # get the previous contributors to that execution of the aggregation
                                for prevstep in chase:
                                    if prevstep == step:
                                        break
                                    if prevstep['rule']:
                                        # if the step features the same aggregation formula
                                        # prevaggregationmatch = re.search(r"(\w)=msum\(.+?\)", prevstep['rule'])
                                        if 'msum' in prevstep['rule']:
                                            prevaggregationmatch = prevstep['rule'].split(', ')[-1]
                                        # if the aggregation formula is the same as the current chase step
                                            if prevaggregationmatch == aggregation:
                                                prevfact = prevstep['name']
                                                # if the name of the fact is the same as the current chase step
                                                if prevfact[:prevfact.find("(")] == fact[:fact.find("(")]:
                                                    prevfactargs = re.findall(r'\((.*?)\)', prevfact)[0]
                                                    prevfactargs_pos = {}
                                                    # print(prevfactargs)
                                                    # get the values in the previous fact for the positions
                                                    # corresponding to the ones in the group-by arguments
                                                    for i, arg in enumerate(prevfactargs.split(',')):
                                                        if i in groupbyvalues_pos:
                                                            prevfactargs_pos[i] = arg

                                                    # check that each value in a position corresponding to the
                                                    # group-by args is the same as the current chase step
                                                    if prevfactargs_pos != groupbyvalues_pos:
                                                        continue

                                                    # update the provenance of the current step
                                                    # with the one of the previous contributor
                                                    provenance = step['provenance'].split('[')[1].split(']')[0].split(', ')
                                                    prevprovenance = prevstep['provenance'].split('[')[1].split(']')[0].split(', ')
                                                    provenance.extend(prevprovenance)
                                                    provenance = list(dict.fromkeys(provenance))
                                                    provenance = self.combination_contributors(provenance, step['rule'], step['name'])
                                                    step['provenance'] = "[" + ", ".join(provenance) + "]"

                        # write chase step with updated provenance in the new json file
                        nstep = {'name': step['name'],
                                 'pattern': step['pattern'],
                                 'provenance': step['provenance'],
                                 'rule': step['rule']}
                        if first_step:
                            first_step = False
                        else:
                            nc.write('\n,')
                        json.dump(nstep, nc, separators=(",", ":"))
                    nc.write('\n]')
        except Exception as e:
            print(f"An error occurred: {e}")



    '''
       This method parses a .csv file into a .txt file with the records as strings
       
       :param csv_path: the path to the csv.json file with the chase graph
       :param output_path: path to output file
       :param hasHeader: if the .csv file has a header as first line
    '''
    def parse_csv_to_txt(self, csv_path, output_path, has_header):
        try:
            with open(csv_path, 'r', newline='') as csv_file:
                pred_name = os.path.splitext(os.path.basename(csv_path))[0]
                reader = csv.reader(csv_file, delimiter=',')
                with open(output_path, "w") as txt_file:
                    for record in reader:
                        if has_header:
                            has_header = False
                        else:
                            record_string = ','.join(record)
                            fact = pred_name + "(" + record_string + ")"
                            txt_file.write(fact + '\n')
        except Exception as e:
            print(f"An error occurred: {e}")