import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2191 : checkSingleBlackFast (-92, -65) 14176 .north (34, 26) (-60, -42) = true := by
  decide +kernel

end LangtonsAnt
