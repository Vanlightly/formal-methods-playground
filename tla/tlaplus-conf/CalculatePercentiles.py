import getopt
import os
import sys

import pandas

def main(argv):
    arg_gb=""
    arg_value_col=""
    arg_in_csv_file=""
    arg_out_csv_file=""

    try:
        opts, args = getopt.getopt(argv, "g:v:i:o:", ["groupbycols=", "valuecol=", "csvin=", "csvout="])
    except getopt.GetoptError:
        print("Error!")
        sys.exit(2)
    for opt, arg in opts:
        if opt in ('-g', "--groupbycols"):
            arg_gb = arg
        elif opt in ("-v", "--valuecol"):
            arg_value_col = arg
        elif opt in ("-i", "--csvin"):
            arg_in_csv_file = arg
        elif opt in ("-o", "--csvout"):
            arg_out_csv_file = arg

    group_by_cols = arg_gb.split(",")
    # out_csv_file = "agg_" + arg_value_col + "__" + os.path.basename(arg_in_csv_file)
    print("Reading file " + arg_in_csv_file)
    df = pandas.read_csv(arg_in_csv_file)
    result = df.groupby(group_by_cols).agg(runs = (arg_value_col,'count'),
                                           min_val = (arg_value_col,'min'),
                                           percentile_50 = (arg_value_col,lambda x: x.quantile(0.5)),
                                           percentile_75 = (arg_value_col,lambda x: x.quantile(0.75)),
                                           percentile_90=(arg_value_col, lambda x: x.quantile(0.9)),
                                           percentile_95 = (arg_value_col, lambda x: x.quantile(0.95)),
                                           percentile_99=(arg_value_col, lambda x: x.quantile(0.99)),
                                           max_val=(arg_value_col, 'max'))

    result.to_csv(arg_out_csv_file, sep=',')
    print("Written aggregated data to " + arg_out_csv_file)

if __name__ == '__main__':
    main(sys.argv[1:])