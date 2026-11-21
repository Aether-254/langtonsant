import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1877 : checkSingleBlackFast (-60, -41) 20920 .north (32, 28) (-58, -20) = true := by
  decide +kernel

end LangtonsAnt
