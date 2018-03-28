import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
import click
import os

configurations = ['DPLLBaseline', 'DPLLWithoutPure', 'DPLLTseitin', 'CDCLBaseline', 'CDCLTseitin', 'CDCLWithoutLearning']
CONFIGURATIONS = []

colors = ['firebrick', 'teal']

RESULTS_FOLDER = os.path.join(os.pardir, 'random/')

class Plotter:
    def __init__(self):
        self.data = {}


    def loadFiles(self, folder, configs):
        shift = 0.3
        for c in configs:
            filename = '{}/{}.time'.format(folder,c)
            print (filename)
            if os.path.exists(filename):
                print('{} {}'.format(c, filename))
                with open(filename) as f:
                    content = f.read()
                    content = content.split('\n')
                    content = list(filter(None, content))
                    content = list(filter(lambda x: "timeout" not in x, content))
                    print (content)
                    yAxis = [float(i.split(' ')[1]) for i in content]
                    xAxis = [int(float(i.split(' ')[0])) + shift for i in content]
                    self.data[c] = {}
                    self.data[c]['x'] = xAxis
                    self.data[c]['y'] = yAxis
            shift = 0

    def plot(self, first, second):
        plt.title('{} vs. {}'.format(first, second))
        plt.ylabel('Avg. runtime of 15 runs in [ms]. First 5 dropped.')
        plt.xlabel('Number of variables in CNF')

        plt.legend(loc=2)
        f = '../{}_vs_{}.png'.format(first,second)

        legend1 = mpatches.Patch(color=colors[0], label=first)
        legend2 = mpatches.Patch(color=colors[1], label=second)

        self.set_ticks(first, colors[0])
        self.set_ticks(second, colors[1])
        plt.legend(handles=[legend1,legend2])
        plt.savefig(f, format='png', dpi=900)
        plt.show()

    def set_ticks(self, config, color):
        x = self.data[config]['x']        
        y = self.data[config]['y']
        print (x)
        print (y)
        #ax.semilogy(np.log10(x), y)        
        plt.semilogy(x,y,markeredgecolor=color, marker='o', ls='', markerfacecolor='none', markeredgewidth=1)

def createConfigs():
    for type in ['Random', 'Examples', 'Structured']:
        for config in configurations:
            CONFIGURATIONS.append('{}_{}'.format(type, config))

@click.command()
@click.argument('first')
@click.argument('second')
def main(first, second):
    createConfigs()
    e = Plotter()
    print(CONFIGURATIONS)
    e.loadFiles(RESULTS_FOLDER, [first, second])
    e.plot(first, second)


if __name__ == '__main__':
    main()

