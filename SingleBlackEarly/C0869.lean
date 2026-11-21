import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0869 : checkSingleBlackFast (-7, -1) 13025 .east (-2, -13) (-27, -9) = true := by
  decide +kernel

end LangtonsAnt
