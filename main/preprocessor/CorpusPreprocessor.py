import os
import logging
import sys

rpath = os.path.abspath('main/preprocessor')
sys.path.append(rpath)
import FilePreprocessor
import importlib
importlib.reload(FilePreprocessor)

'''
    This class collects preprocessing and rewriting operations
    over input files to adapt them for the fine-tuning pipeline
    
    __author__: teodorobaldazzi
    __author__: andreacolombo
'''
class CorpusPreprocessor:

    logging.getLogger().setLevel(logging.INFO)


    '''
        :param csv_file_names:
        :param output_path:
        :param csv_output_path:
    '''
    def get_list_output_facts(self, csv_file_names, output_path, csv_output_path):

        lines = list()

        for name in csv_file_names:
            FilePreprocessor.FilePreprocessor().parse_csv_to_txt(os.path.join(csv_output_path, name + '.csv'), os.path.join(output_path, name + '.txt'), True)
            with open(os.path.join(output_path, name + '.txt')) as f:
                lines.append(f.readlines())
                for i in range(len(lines[-1])):
                    lines[-1][i] = lines[-1][i].replace('\n','')

            if os.path.exists(os.path.join(output_path, name + '.txt')):
                os.remove(os.path.join(output_path, name + '.txt'))
    
        for i in range(1,len(lines)):
            lines[0] += lines[i]
        facts_to_explain = lines[0]

        return(facts_to_explain)