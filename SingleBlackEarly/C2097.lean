import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2097 : checkSingleBlackFast (-80, -61) 21960 .north (42, 38) (-68, -30) = true := by
  decide +kernel

end LangtonsAnt
