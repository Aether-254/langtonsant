import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0685 : checkSingleBlackFast (19, -9) 8569 .west (-16, 8) (-22, -23) = true := by
  decide +kernel

end LangtonsAnt
