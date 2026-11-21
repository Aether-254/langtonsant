import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0848 : checkSingleBlackFast (-7, 9) 30055 .east (12, -13) (-36, -6) = true := by
  decide +kernel

end LangtonsAnt
