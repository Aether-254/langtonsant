import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2125 : checkSingleBlackFast (-86, -59) 13864 .north (31, 23) (-57, -39) = true := by
  decide +kernel

end LangtonsAnt
