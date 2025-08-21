# create_plots.py

# Script that defines functions to plot the data obtained in the final results of the four solvers measured
# with the entire integration-test and the complete timeout of 15 minutes (DepQBF, Naive, NaivePre and INF final).
# We have created the following plots:
# * Barplots with the number (and percentage) of the resolved instances
# * Barplots with the mean walltimes needed for solving the instances, with a penalization of 2*TIMEOUT (30 min)
#   in the case of instances that the solver couldn't solve
# * Barplot with additional min and max information about the memory usage of the solvers.
# * Performance profiles or cactus-plots with the four solvers: x-axis for spent (or available) time and y-axis for
#   the number of resolved instances.

import csv
import matplotlib.pyplot as plt
import numpy as np

def create_barplot_correct_num() -> None:
    # Leer CSV usando módulo csv
    solvers = []
    correct_num = []
    correct_per = []

    with open("../Benchmark_aggregates.csv", newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            solvers.append(row["solver_name"])
            correct_num.append(int(row["correct_num"]))
            correct_per.append(float(row["correct_per"]))

    # Crear figura
    fig, ax = plt.subplots(figsize=(8, 5))

    # Crear barras
    bars = ax.bar(solvers, correct_num, color="skyblue", edgecolor="black")

    # Añadir texto encima de las barras
    for bar, num, perc in zip(bars, correct_num, correct_per):
        ax.text(
            bar.get_x() + bar.get_width() / 2,
            bar.get_height() + 2,
            f"{num} ({perc:.2%})",
            ha="center", va="bottom", fontsize=10, fontweight="bold"
        )

    # Etiquetas y título
    ax.set_ylabel("")
    ax.set_xlabel("")
    ax.set_title("Número y porcentaje de instancias correctas")
    ax.set_ylim(0, max(correct_num) * 1.15)
    ax.grid(axis="y", linestyle="--", alpha=0.7)

    plt.tight_layout()
    plt.show()


def create_barplot_walltime() -> None:
    # Leer CSV usando módulo csv
    solvers = []
    wall_times = []

    with open("../Benchmark_aggregates.csv", newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            solvers.append(row["solver_name"])
            wall_times.append(float(row['wall_time_penalized_s_mean']))

    # Crear figura
    fig, ax = plt.subplots(figsize=(8, 5))

    # Crear barras
    bars = ax.bar(solvers, wall_times, color="salmon", edgecolor="black")

    # Añadir texto encima de las barras
    for bar, time in zip(bars, wall_times):
        ax.text(
            bar.get_x() + bar.get_width() / 2,
            bar.get_height() + 2,
            f"{time:.2f}",
            ha="center", va="bottom", fontsize=10, fontweight="bold"
        )

    # Etiquetas y título
    ax.set_ylabel("")
    ax.set_xlabel("")
    ax.set_title("Media de los tiempos reales en segundos con penalización")
    ax.set_ylim(0, max(wall_times) * 1.15)
    ax.grid(axis="y", linestyle="--", alpha=0.7)

    plt.tight_layout()
    plt.show()


def create_barplot_memory() -> None:
    # Leer CSV
    solvers = []
    mem_mean = []
    mem_min = []
    mem_max = []

    with open("../Benchmark_aggregates.csv", newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            solvers.append(row["solver_name"])
            mem_mean.append(float(row["memory_peak_mb_mean"]))
            mem_min.append(float(row["memory_peak_mb_min"]))
            mem_max.append(float(row["memory_peak_mb_max"]))

    # Calcular rangos para error bars
    errors_lower = [mean - minv for mean, minv in zip(mem_mean, mem_min)]
    errors_upper = [maxv - mean for mean, maxv in zip(mem_mean, mem_max)]

    # Posiciones para las barras
    x = np.arange(len(solvers))

    # Crear figura
    fig, ax = plt.subplots(figsize=(8, 5))

    # Dibujar barras con error bars asimétricas
    bars = ax.bar(x, mem_mean, yerr=[errors_lower, errors_upper],
                capsize=5, color="lightgreen", edgecolor="black", zorder=2)

    # Escala logarítmica
    ax.set_yscale("log")

    # Añadir etiquetas desplazadas
    for i, (bar, mean, minv, maxv) in enumerate(zip(bars, mem_mean, mem_min, mem_max)):
        # Posición central de la barra
        bar_x = bar.get_x() + bar.get_width() / 2

        # Texto del valor medio (a la derecha de la barra)
        ax.text(bar_x + 0.05, mean * 1.25, f"{mean:.1f}",
                ha="left", va="center", fontsize=9, fontweight="bold")

        # Texto del valor mínimo (debajo de la línea inferior)
        ax.text(bar_x, minv / 1.1, f"{minv:.1f}",
                ha="center", va="top", fontsize=8, color="blue")

        # Texto del valor máximo (encima de la línea superior)
        ax.text(bar_x, maxv * 1.05, f"{maxv:.1f}",
                ha="center", va="bottom", fontsize=8, color="red")

    # Ajustes de gráfico
    ax.set_xticks(x)
    ax.set_xticklabels(solvers)
    ax.set_ylabel("")
    ax.set_title("Memoria pico en MB (media, mínimo y máximo) en escala logarítmica")
    ax.grid(axis="y", linestyle="--", alpha=0.7, zorder=1)

    plt.tight_layout()
    plt.show()


def create_performance_profile() -> None:
    zoom = "general" # | "local" | ("micro")
    if zoom == "general":
        x = np.arange(0, 10, 0.1).tolist() + list(range(10, 311, 10))
    elif zoom == "local":
        x = np.arange(0, 1, 0.05).tolist() + list(range(1, 21, 1))
    else:
        x = np.arange(0, 1, 0.05).tolist() + list(range(1, 6, 1))

    result_files = ('../DepQBF_benchmark_results.csv', '../Naive_benchmark_results.csv',
                    '../NaivePre_benchmark_results.csv', '../FNI_benchmark_results.csv')

    labels = ('DepQBF', 'Naive', 'NaivePre', 'FNI')
    markers = ('o', 's', '^', 'D')

    # Crear gráfico
    plt.figure(figsize=(8,5))

    for file, label, marker in zip(result_files, labels, markers):
        y = []

        with open(file, 'r', newline='') as f:
            reader = csv.DictReader(f)
            instance_times = [float(row['total_wall_time']) for row in reader]
        
        for time in x:
            num_solved_in_time = len([t for t in instance_times if t <= time])
            y.append(num_solved_in_time)

        plt.plot(x, y, marker=marker, label=label)

    # Etiquetas y título
    plt.xlabel("Tiempo (s)")
    plt.ylabel("Instancias resueltas")
    plt.title("Número de instancias resueltas según el tiempo disponible")
    plt.grid(True, linestyle="--", alpha=0.7)

    # Leyenda
    plt.legend()

    plt.tight_layout()
    plt.show()


if __name__ == '__main__':
    #create_barplot_correct_num()
    #create_barplot_walltime()
    #create_barplot_memory()
    create_performance_profile()