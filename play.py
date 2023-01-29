from sklearn.tree import DecisionTreeClassifier, export_graphviz
from sklearn.datasets import load_iris

data = load_iris()
X, y = data['data'], data['target']

dct = DecisionTreeClassifier()
dct.fit(X, y)

export_graphviz(dct, out_file='test.dot')