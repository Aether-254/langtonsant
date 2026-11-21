import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1181 : checkSingleBlackFast (27, -1) 14103 .west (-17, 12) (-29, -27) = true := by
  decide +kernel

end LangtonsAnt
