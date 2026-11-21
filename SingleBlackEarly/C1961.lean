import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1961 : checkSingleBlackFast (-71, -47) 14991 .west (22, 33) (-52, 14) = true := by
  decide +kernel

end LangtonsAnt
