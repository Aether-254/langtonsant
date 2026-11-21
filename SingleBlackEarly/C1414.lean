import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1414 : checkSingleBlackFast (-20, 1) 19208 .north (-6, 2) (-2, -28) = true := by
  decide +kernel

end LangtonsAnt
