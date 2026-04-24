export type Mutation = {
  name: string;
  status: string;
  position: number | null;
  matched_pattern: string;
  quality_score: number | null;
  confidence: string;
  notes: string;
};

export type LowQualityRegion = {
  start: number;
  end: number;
  average_quality: number;
};

export type APIResult = {
  ok: boolean;
  file_name: string;
  primer_type: string;
  qc: {
    sequence_length: number;
    average_quality: number | null;
    low_quality_regions: LowQualityRegion[];
    warnings: string[];
  };
  analysis: {
    primer_type: string;
    sequence_length: number;
    mutations: Mutation[];
    warnings: string[];
  };
  report: {
    warnings: string[];
    disclaimer: string;
  };
};

export type APIError = {
  ok: false;
  error: {
    code: string;
    message: string;
  };
};
