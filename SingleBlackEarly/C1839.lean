import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1839 : checkSingleBlackFast (-60, -33) 12512 .north (18, 10) (-44, -26) = true := by
  decide +kernel

end LangtonsAnt
