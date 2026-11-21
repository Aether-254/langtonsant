import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2057 : checkSingleBlackFast (-75, -57) 13360 .north (27, 19) (-53, -35) = true := by
  decide +kernel

end LangtonsAnt
