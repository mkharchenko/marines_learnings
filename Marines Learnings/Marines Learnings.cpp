#include <iostream>
#include <vector>
#include <string>
#include <deque>

const int INFINITY_VALUE = 1000000000;
const int INDEXING_SHIFT = 1;
const char NO_SUCH_FLOW_MESSAGE[] = "-1";
const int EDGE_CAPACITY = 1;
enum EdgeStatus {
    STATUS_NOT_PROCESSED,
    STATUS_IN_PROCESS,
    STATUS_PROCESSED,
};

struct Edge {
    int from, to, capacity, cost, flow;
    size_t back;
    int number;
};

struct MinCostFlowAnswer {
    int total_flow, total_cost;
};

class MinCostFlow {
private:
    std::vector<std::vector<Edge>> graph;
    std::vector<Edge> edges;
    int islands_number;
    int bridges_number;
    int soldiers_number;

    Edge normalizeEdge(const Edge& edge) {
        Edge normalized_edge = edge;
        normalized_edge.from -= INDEXING_SHIFT;
        normalized_edge.to -= INDEXING_SHIFT;
        return normalized_edge;
    }

    // Добавление ребра в граф
    void addGraphEdge(const Edge& edge) {
        const Edge normalized_edge = normalizeEdge(edge);
        Edge bridge = {
            normalized_edge.from,
            normalized_edge.to, normalized_edge.capacity, normalized_edge.cost,
            0, graph[normalized_edge.to].size(), normalized_edge.number
        };
        Edge reversed_bridge = {
            normalized_edge.to, normalized_edge.from,
            0, normalized_edge.cost * -1,
            0, graph[normalized_edge.from].size(), normalized_edge.number
        };
        graph[normalized_edge.from].push_back(bridge);
        graph[normalized_edge.to].push_back(reversed_bridge);
        Edge back_bridge = { normalized_edge.to,
            normalized_edge.from, edge.capacity, normalized_edge.cost,
            0, graph[normalized_edge.from].size(), normalized_edge.number
        };
        Edge reversed_back_bridge = { back_bridge.to, back_bridge.from, 0,
            back_bridge.cost * -1, 0, graph[back_bridge.from].size(),
            back_bridge.number
        };
        graph[back_bridge.from].push_back(back_bridge);
        graph[back_bridge.to].push_back(reversed_back_bridge);
    }

    // Формирование исходного графа
    void formGraph(const std::vector<Edge>& edges) {
        const int edges_size = edges.size();
        graph.resize(islands_number);
        for (int i = 0; i < edges_size; ++i) {
            addGraphEdge(edges[i]);
        }
    }

public:
    explicit MinCostFlow(const int islands_number,
        const int bridges_number,
        const int soldiers_number,
        const std::vector<Edge>& edges) {
        this->islands_number = islands_number;
        this->bridges_number = bridges_number;
        this->soldiers_number = soldiers_number;
        this->edges = edges;
        formGraph(edges);
    }

    // Нахождение пути минимальной стоимости
    MinCostFlowAnswer findMinCostFlow() {
        const int islands_number = graph.size();
        MinCostFlowAnswer min_cost_flow_answer{ 0, 0 };
        const int source = 0, sink = islands_number - 1;
        while (min_cost_flow_answer.total_flow < soldiers_number) {
            std::vector<int> node_status(islands_number, STATUS_NOT_PROCESSED);
            std::vector<int> distance_between_nodes(islands_number,
                INFINITY_VALUE);
            std::deque<int> nodes_queue(islands_number);
            std::vector<int> parent_nodes(islands_number);
            std::vector<size_t> parent_edges(islands_number);
            nodes_queue.push_back(source);
            distance_between_nodes[source] = 0;
            while (!nodes_queue.empty()) {
                const int current_node = nodes_queue.front();
                nodes_queue.pop_front();
                if (current_node < islands_number) {
                    node_status[current_node] = STATUS_PROCESSED;
                }
                else {
                    throw new std::out_of_range(
                        "Current node number out of range.");
                }
                for (int i = 0; i < graph[current_node].size(); ++i) {
                    Edge& current_edge = graph[current_node][i];

                    if (current_edge.from >= islands_number ||
                        current_edge.to >= islands_number) {
                        throw new std::invalid_argument(
                            "Invalid current edge.");
                    }

                    const int current_distance =
                        distance_between_nodes[current_node];
                    const int next_distance =
                        distance_between_nodes[current_edge.to];
                    if (current_edge.flow < current_edge.capacity
                        && current_distance + current_edge.cost
                        < next_distance) {
                        distance_between_nodes[current_edge.to] =
                            distance_between_nodes[current_node] +
                            current_edge.cost;
                        if (node_status[current_edge.to] ==
                            STATUS_NOT_PROCESSED) {
                            nodes_queue.push_back(current_edge.to);
                        }
                        else if (node_status[current_edge.to] ==
                            STATUS_PROCESSED) {
                            nodes_queue.push_front(current_edge.to);
                        }
                        node_status[current_edge.to] = STATUS_IN_PROCESS;
                        parent_nodes[current_edge.to] = current_node;
                        parent_edges[current_edge.to] = i;
                    }
                }
            }
            if (distance_between_nodes[sink] == INFINITY_VALUE) {
                break;
            }
            for (int current_node = sink; current_node != source;
                current_node = parent_nodes[current_node]) {
                const int parent_node = parent_nodes[current_node];
                size_t parent_edge = parent_edges[current_node];
                size_t back_parent_edge = 0;
                if (parent_node < graph.size()) {
                    if (parent_edge < graph[parent_node].size()) {
                        back_parent_edge =
                            graph[parent_node][parent_edge].back;
                    }
                    else {
                        throw new std::out_of_range(
                            "Parent edge out of range.");
                    }
                }
                else {
                    throw new std::out_of_range("Parent node out of range.");
                }
                graph[parent_node][parent_edge].flow += EDGE_CAPACITY;
                graph[current_node][back_parent_edge].flow -= EDGE_CAPACITY;
                min_cost_flow_answer.total_cost +=
                    graph[parent_node][parent_edge].cost;
            }
            min_cost_flow_answer.total_flow += EDGE_CAPACITY;
        }
        return min_cost_flow_answer;
    }

    // Восстановление путей пехотинцев
    std::vector<int> getRestoredPath() {
        std::vector<int> way;

        const int source = 0, sink = islands_number - 1;

        int current_node = source;
        while (current_node != sink) {
            if (current_node < islands_number) {
                for (int current_edge = 0; current_edge <
                    graph[current_node].size(); ++current_edge) {
                    if (graph[current_node][current_edge].flow > 0) {
                        way.push_back(graph[current_node]
                            [current_edge].number + 1);
                        graph[current_node][current_edge].flow = 0;
                        current_node =
                            graph[current_node][current_edge].to;
                    }
                }
            }
            else {
                throw new std::out_of_range("Current node out of range");
            }
        }
        return way;
    }
};

// Считывание количества островов
int readNumberOfIslands(std::istream& input = std::cin) {
    int islands_number;
    input >> islands_number;
    return islands_number;
}

// Считывание количества мостов
int readNumberOfBridges(std::istream& input = std::cin) {
    int bridges_number;
    input >> bridges_number;
    return bridges_number;
}

// Считывание количества солдат
int readNumberOfSoldiers(std::istream& input = std::cin) {
    int soldiers_number;
    input >> soldiers_number;
    return soldiers_number;
}

// Считывание мостов
std::vector<Edge> readEdges(const int bridges_number,
    std::istream& input = std::cin) {
    std::vector<Edge> edges(bridges_number);
    for (int i = 0; i < bridges_number; ++i) {
        Edge edge;
        input >> edge.from >> edge.to >> edge.cost;
        edge.number = i;
        edge.capacity = EDGE_CAPACITY;
        edges[i] = edge;
    }
    return edges;
}

// Нормализация данных и решение задачи
std::string findMinCostFlow(const int islands_number,
    const int bridges_number,
    const int soldiers_number,
    const std::vector<Edge>& edges) {
    MinCostFlow min_cost_flow = MinCostFlow(islands_number, bridges_number,
        soldiers_number, edges);
    const MinCostFlowAnswer min_cost_flow_answer =
        min_cost_flow.findMinCostFlow();
    std::string answer_string = "";
    if (min_cost_flow_answer.total_flow < soldiers_number) {
        answer_string = NO_SUCH_FLOW_MESSAGE;
        return answer_string;
    }

    const double flow_mean_cost = static_cast<double>
        (min_cost_flow_answer.total_cost) /
        static_cast<double>(soldiers_number);
    answer_string += std::to_string(flow_mean_cost) + "\n";

    for (int i = 0; i < soldiers_number; ++i) {
        std::vector<int> way = min_cost_flow.getRestoredPath();
        answer_string += std::to_string(way.size()) + " ";
        for (int i = 0; i < way.size(); ++i) {
            answer_string += std::to_string(way[i]) + " ";
        }
        answer_string += "\n";
    }

    return answer_string;
}

// Вывод результата задачи
void writeMinCostFlowAnswer(std::string answer_string,
    std::ostream& output = std::cout) {
    output << answer_string;
}

int main()
{
    const int islands_number = readNumberOfIslands();
    const int bridges_number = readNumberOfBridges();
    const int soldiers_number = readNumberOfSoldiers();
    const std::vector<Edge> edges = readEdges(bridges_number);
    const std::string answer_string = findMinCostFlow(islands_number,
        bridges_number, soldiers_number, edges);
    writeMinCostFlowAnswer(answer_string);
}
