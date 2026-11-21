import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1029 : checkSingleBlackFast (-8, 18) 10644 .north (1, 0) (-27, 6) = true := by
  decide +kernel

end LangtonsAnt
